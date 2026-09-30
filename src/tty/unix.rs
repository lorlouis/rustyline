//! Unix specific definitions
use std::cmp;
use std::collections::HashMap;
#[cfg(feature = "kitty-keyboard-protocol")]
use std::collections::VecDeque;
use std::fs::{File, OpenOptions};
#[cfg(not(feature = "buffer-redux"))]
use std::io::BufReader;
use std::io::{self, ErrorKind, Read, Write as _};
use std::os::fd::{AsFd, AsRawFd as _, BorrowedFd, IntoRawFd, RawFd};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::mpsc::{self, SyncSender};
use std::sync::{Arc, Mutex};

#[cfg(feature = "buffer-redux")]
use buffer_redux::BufReader;
use log::{debug, warn};
use nix::errno::Errno;
use nix::poll::{self, PollFlags, PollTimeout};
use nix::sys::select::{self, FdSet};
#[cfg(not(feature = "termios"))]
use nix::sys::termios::Termios;
use nix::sys::time::TimeValLike as _;
use nix::unistd::{close, isatty, read, write};
#[cfg(feature = "termios")]
use termios::Termios;
use unicode_segmentation::UnicodeSegmentation as _;
use utf8parse::{Parser, Receiver};

use super::{Event, RawMode, RawReader, Renderer, Term, width};
use crate::config::{Behavior, BellStyle, ColorMode, Config};
use crate::error::Signal;
use crate::highlight::Highlighter;
use crate::keys::{KeyCode as K, KeyEvent, KeyEvent as E, Modifiers as M};
use crate::layout::{GraphemeClusterMode, Layout, Position, Unit};
use crate::line_buffer::LineBuffer;
use crate::{Cmd, Prompt, ReadlineError, Result, error};

const BRACKETED_PASTE_ON: &str = "\x1b[?2004h";
const BRACKETED_PASTE_OFF: &str = "\x1b[?2004l";
const BEGIN_SYNCHRONIZED_UPDATE: &str = "\x1b[?2026h";
const END_SYNCHRONIZED_UPDATE: &str = "\x1b[?2026l";
#[cfg(feature = "kitty-keyboard-protocol")]
const KITTY_ENABLE: &str = "\x1b[>1u";
#[cfg(feature = "kitty-keyboard-protocol")]
const KITTY_DISABLE: &str = "\x1b[<u";
#[cfg(feature = "kitty-keyboard-protocol")]
const KITTY_PROBE: &str = "\x1b[?u\x1b[c";
#[cfg(feature = "kitty-keyboard-protocol")]
const KITTY_PROBE_TIMEOUT_MS: u16 = 100;

/// State of the kitty keyboard protocol on a unix terminal.
///
/// `Confirmed` means the terminal supports the protocol and it is enabled in
/// the current raw session. `Unsupported` is the cached result of a probe
/// that found the terminal does not support it (so we don't probe again).
/// `Off` is the default (not enabled, and not probed or probe pending).
#[cfg(feature = "kitty-keyboard-protocol")]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum KittyDetection {
    /// Not enabled (not requested, not yet probed, or probe pending).
    #[default]
    Off,
    /// Probed: the terminal does not support the protocol.
    Unsupported,
    /// Probed: the terminal supports the protocol and it is enabled in the
    /// current raw session.
    Confirmed,
}

nix::ioctl_read_bad!(win_size, libc::TIOCGWINSZ, libc::winsize);

fn get_win_size(fd: AltFd) -> (Unit, Unit) {
    use std::mem::zeroed;

    if cfg!(test) {
        return (80, 24);
    }

    unsafe {
        let mut size: libc::winsize = zeroed();
        match win_size(fd.0, &raw mut size) {
            Ok(0) => {
                // In linux pseudo-terminals are created with dimensions of
                // zero. If host application didn't initialize the correct
                // size before start we treat zero size as 80 columns and
                // infinite rows
                let cols = if size.ws_col == 0 { 80 } else { size.ws_col };
                let rows = if size.ws_row == 0 {
                    Unit::MAX
                } else {
                    size.ws_row
                };
                (cols, rows)
            }
            _ => (80, 24),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct AltFd(RawFd);
impl IntoRawFd for AltFd {
    #[inline]
    fn into_raw_fd(self) -> RawFd {
        self.0
    }
}
impl AsFd for AltFd {
    #[inline]
    fn as_fd(&self) -> BorrowedFd<'_> {
        unsafe { BorrowedFd::borrow_raw(self.0) }
    }
}

/// Return whether or not STDIN, STDOUT or STDERR is a TTY
fn is_a_tty(fd: AltFd) -> bool {
    isatty(fd).unwrap_or(false)
}

#[cfg(any(not(feature = "buffer-redux"), test))]
pub type PosixBuffer = ();
#[cfg(all(feature = "buffer-redux", not(test)))]
pub type PosixBuffer = buffer_redux::Buffer;
#[cfg(not(test))]
pub type Buffer = PosixBuffer;

pub type PosixKeyMap = HashMap<KeyEvent, Cmd>;
#[cfg(not(test))]
pub type KeyMap = PosixKeyMap;

#[must_use = "You must restore default mode (disable_raw_mode)"]
pub struct PosixMode {
    termios: Termios,
    tty_in: AltFd,
    tty_out: Option<AltFd>,
    raw_mode: Arc<AtomicBool>,
    /// Output fd to restore the kitty keyboard protocol on, independent of
    /// the bracketed-paste `tty_out` (which is `None` when bracketed paste is
    /// disabled). `Some` only when the protocol is active (`Confirmed`).
    #[cfg(feature = "kitty-keyboard-protocol")]
    kitty_out: Option<AltFd>,
}

#[cfg(not(test))]
pub type Mode = PosixMode;

impl RawMode for PosixMode {
    /// Disable RAW mode for the terminal.
    fn disable_raw_mode(&self) -> Result<()> {
        termios_::disable_raw_mode(self.tty_in, &self.termios)?;
        // disable bracketed paste
        if let Some(out) = self.tty_out {
            write_all(out, BRACKETED_PASTE_OFF)?;
        }
        // restore the kitty keyboard protocol mode
        #[cfg(feature = "kitty-keyboard-protocol")]
        if let Some(out) = self.kitty_out {
            write_all(out, KITTY_DISABLE)?;
            #[cfg(not(feature = "signal-hook"))]
            clear_kitty_sigstop_handler();
        }
        self.raw_mode.store(false, Ordering::SeqCst);
        Ok(())
    }
}

// Rust std::io::Stdin is buffered with no way to know if bytes are available.
// So we use low-level stuff instead...
struct TtyIn {
    fd: AltFd,
    sig: Option<Sig>,
}

impl Read for TtyIn {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        loop {
            let res = unsafe {
                libc::read(
                    self.fd.0,
                    buf.as_mut_ptr().cast::<libc::c_void>(),
                    buf.len() as libc::size_t,
                )
            };
            if res == -1 {
                let error = io::Error::last_os_error();
                if error.kind() == ErrorKind::Interrupted {
                    if let Some(signal) = self.sig()? {
                        return Err(io::Error::new(
                            ErrorKind::Interrupted,
                            error::SignalError(signal),
                        ));
                    }
                } else {
                    return Err(error);
                }
            } else {
                #[expect(clippy::cast_sign_loss)]
                return Ok(res as usize);
            }
        }
    }
}
#[expect(unused_must_use)]
impl Drop for TtyIn {
    fn drop(&mut self) {
        if let Some(sig) = self.sig.take() {
            sig.uninstall_sigwinch_handler();
        }
    }
}

impl TtyIn {
    /// Check if a signal has been received
    fn sig(&self) -> nix::Result<Option<Signal>> {
        if let Some(pipe) = self.sig_fd() {
            let mut buf = [0u8; 64];
            match read(pipe, &mut buf) {
                Ok(0) => Ok(None),
                Ok(_) => Ok(Some(Signal::from(buf[0]))),
                Err(e) if e == Errno::EWOULDBLOCK || e == Errno::EINTR => Ok(None),
                Err(e) => Err(e),
            }
        } else {
            Ok(None)
        }
    }

    fn sig_fd(&self) -> Option<BorrowedFd<'_>> {
        self.sig.as_ref().map(|s| s.pipe.as_fd())
    }
}

// (native receiver with a selectable file descriptor, actual message receiver)
type PipeReader = Arc<Mutex<(File, mpsc::Receiver<String>)>>;
// (native sender, actual message sender)
type PipeWriter = (Arc<Mutex<File>>, SyncSender<String>);

/// Console input reader
pub struct PosixRawReader {
    tty_in: BufReader<TtyIn>,
    timeout_ms: PollTimeout,
    /// Kitty keyboard protocol is active on this terminal
    #[cfg(feature = "kitty-keyboard-protocol")]
    kitty: bool,
    /// Bytes to be returned before reading from the input
    /// (only used when the kitty keyboard protocol is enabled)
    #[cfg(feature = "kitty-keyboard-protocol")]
    pushback: VecDeque<u8>,
    parser: Parser,
    key_map: PosixKeyMap,
    // external print reader
    pipe_reader: Option<PipeReader>,
    #[cfg(target_os = "macos")]
    is_dev_tty: bool,
}

impl AsFd for PosixRawReader {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.tty_in.get_ref().fd.as_fd()
    }
}

struct Utf8 {
    c: Option<char>,
    valid: bool,
}

const UP: char = 'A'; // kcuu1, kUP*
const DOWN: char = 'B'; // kcud1, kDN*
const RIGHT: char = 'C'; // kcuf1, kRIT*
const LEFT: char = 'D'; // kcub1, kLFT*
const END: char = 'F'; // kend*
const HOME: char = 'H'; // khom*
const INSERT: char = '2'; // kic*
const DELETE: char = '3'; // kdch1, kDC*
const PAGE_UP: char = '5'; // kpp, kPRV*
const PAGE_DOWN: char = '6'; // knp, kNXT*

const RXVT_HOME: char = '7';
const RXVT_END: char = '8';

const SHIFT: char = '2';
const ALT: char = '3';
const ALT_SHIFT: char = '4';
const CTRL: char = '5';
const CTRL_SHIFT: char = '6';
const CTRL_ALT: char = '7';
const CTRL_ALT_SHIFT: char = '8';

const RXVT_SHIFT: char = '$';
const RXVT_CTRL: char = '\x1e';
const RXVT_CTRL_SHIFT: char = '@';

impl PosixRawReader {
    // the kitty feature adds 2 arguments, taking this over the 7-arg limit
    #[cfg_attr(
        feature = "kitty-keyboard-protocol",
        expect(clippy::too_many_arguments)
    )]
    fn new(
        fd: AltFd,
        sig: Option<Sig>,
        buffer: Option<PosixBuffer>,
        config: &Config,
        key_map: PosixKeyMap,
        pipe_reader: Option<PipeReader>,
        #[cfg(feature = "kitty-keyboard-protocol")] kitty: bool,
        #[cfg(feature = "kitty-keyboard-protocol")] pending: Vec<u8>,
        #[cfg(target_os = "macos")] is_dev_tty: bool,
    ) -> Self {
        let inner = TtyIn { fd, sig };
        #[cfg(any(not(feature = "buffer-redux"), test))]
        let (tty_in, _) = (BufReader::with_capacity(1024, inner), buffer);
        #[cfg(all(feature = "buffer-redux", not(test)))]
        let tty_in = if let Some(buffer) = buffer {
            BufReader::with_buffer(buffer, inner)
        } else {
            BufReader::with_capacity(1024, inner)
        };
        Self {
            tty_in,
            timeout_ms: config.keyseq_timeout().into(),
            #[cfg(feature = "kitty-keyboard-protocol")]
            kitty,
            #[cfg(feature = "kitty-keyboard-protocol")]
            pushback: VecDeque::from(pending),
            parser: Parser::new(),
            key_map,
            pipe_reader,
            #[cfg(target_os = "macos")]
            is_dev_tty,
        }
    }

    /// Handle \E <seq1> sequences
    // https://invisible-island.net/xterm/xterm-function-keys.html
    fn escape_sequence(&mut self) -> Result<KeyEvent> {
        self.do_escape_sequence(true)
    }

    /// Don't call directly, call `PosixRawReader::escape_sequence` instead
    fn do_escape_sequence(&mut self, allow_recurse: bool) -> Result<KeyEvent> {
        // Read the next byte representing the escape sequence.
        let seq1 = self.next_char()?;
        if seq1 == '[' {
            // \E[ sequences. (CSI)
            self.escape_csi()
        } else if seq1 == 'O' {
            // xterm
            // \EO sequences. (SS3)
            self.escape_o()
        } else if seq1 == '\x1b' {
            // \E\E — used by rxvt, iTerm (under default config), etc.
            // ```
            // \E\E[A => Alt-Up
            // \E\E[B => Alt-Down
            // \E\E[C => Alt-Right
            // \E\E[D => Alt-Left
            // ```
            //
            // In general this more or less works just adding ALT to an existing
            // key, but has a wrinkle in that `ESC ESC` without anything
            // following should be interpreted as the escape key.
            //
            // We handle this by polling to see if there's anything coming
            // within our timeout, and if so, recursing once, but adding alt to
            // what we read.
            if !allow_recurse {
                return Ok(E::ESC);
            }
            let timeout = if self.timeout_ms.is_none() {
                100u8.into()
            } else {
                self.timeout_ms
            };
            match self.poll(timeout) {
                // Ignore poll errors, it's very likely we'll pick them up on
                // the next read anyway.
                Ok(false) | Err(_) => Ok(E::ESC),
                Ok(true) => {
                    // recurse, and add the alt modifier.
                    let E(k, m) = self.do_escape_sequence(false)?;
                    Ok(E(k, m | M::ALT))
                }
            }
        } else {
            Ok(E::alt(seq1))
        }
    }

    /// Handle \E[ escape sequences
    fn escape_csi(&mut self) -> Result<KeyEvent> {
        let seq2 = self.next_char()?;
        #[cfg(feature = "kitty-keyboard-protocol")]
        if self.kitty {
            return self.escape_csi_kitty(seq2);
        }
        self.escape_csi_legacy(seq2)
    }

    /// Handle \E[ <seq2> escape sequences (legacy encoding)
    fn escape_csi_legacy(&mut self, seq2: char) -> Result<KeyEvent> {
        if seq2.is_ascii_digit() {
            match seq2 {
                '0' | '9' => {
                    debug!(target: "rustyline", "unsupported esc sequence: \\E[{seq2:?}");
                    Ok(E(K::UnknownEscSeq, M::NONE))
                }
                _ => {
                    // Extended escape, read additional byte.
                    self.extended_escape(seq2)
                }
            }
        } else if seq2 == '[' {
            let seq3 = self.next_char()?;
            // Linux console
            Ok(match seq3 {
                'A' => E(K::F(1), M::NONE),
                'B' => E(K::F(2), M::NONE),
                'C' => E(K::F(3), M::NONE),
                'D' => E(K::F(4), M::NONE),
                'E' => E(K::F(5), M::NONE),
                _ => {
                    debug!(target: "rustyline", "unsupported esc sequence: \\E[[{seq3:?}");
                    E(K::UnknownEscSeq, M::NONE)
                }
            })
        } else {
            // ANSI
            Ok(match seq2 {
                UP => E(K::Up, M::NONE),
                DOWN => E(K::Down, M::NONE),
                RIGHT => E(K::Right, M::NONE),
                LEFT => E(K::Left, M::NONE),
                //'E' => E(K::, M::), // Ignore
                END => E(K::End, M::NONE),
                //'G' => E(K::, M::), // Ignore
                HOME => E(K::Home, M::NONE), // khome
                //'J' => E(K::, M::), // clr_eos
                //'K' => E(K::, M::), // clr_eol
                //'L' => E(K::, M::), // il1
                //'M' => E(K::, M::), // kmous
                //'P' => E(K::Delete, M::NONE), // dch1
                'Z' => E(K::BackTab, M::NONE),
                'a' => E(K::Up, M::SHIFT),    // rxvt: kind or kUP
                'b' => E(K::Down, M::SHIFT),  // rxvt: kri or kDN
                'c' => E(K::Right, M::SHIFT), // rxvt
                'd' => E(K::Left, M::SHIFT),  // rxvt
                _ => {
                    debug!(target: "rustyline", "unsupported esc sequence: \\E[{seq2:?}");
                    E(K::UnknownEscSeq, M::NONE)
                }
            })
        }
    }

    /// Kitty keyboard protocol: buffer the whole CSI sequence.
    /// If it is a `CSI u` key event, decode it, otherwise push the bytes
    /// back and fall back to the legacy parser.
    #[cfg(feature = "kitty-keyboard-protocol")]
    fn escape_csi_kitty(&mut self, seq2: char) -> Result<KeyEvent> {
        // a `CSI u` key event always starts with a digit (the key code);
        // a non-digit `seq2` is a legacy CSI sequence — parse it directly
        // without reading further bytes (which would consume the next key)
        if !seq2.is_ascii_digit() {
            return self.escape_csi_legacy(seq2);
        }
        let mut csi = vec![b'[', seq2 as u8];
        // a non-ascii char read after `[` (not part of a valid CSI), to be
        // pushed back so it is not lost
        let mut trailing: Option<char> = None;
        loop {
            match self.next_char() {
                Ok(c) => {
                    // CSI sequences are ASCII,
                    // anything else means this is not a valid CSI sequence
                    if !c.is_ascii() {
                        trailing = Some(c);
                        break;
                    }
                    csi.push(c as u8);
                    // final byte of a CSI sequence
                    if matches!(c as u8, 0x40..=0x7e) {
                        break;
                    }
                }
                // input ended in the middle of the sequence
                Err(ReadlineError::Eof) => break,
                Err(e) => return Err(e),
            }
        }
        if csi.last() == Some(&b'u') {
            if let Some(key) = kitty::decode(&csi) {
                return Ok(key);
            }
            debug!(
                target: "rustyline",
                "unsupported kitty key: {}",
                String::from_utf8_lossy(&csi)
            );
            return Ok(E(K::UnknownEscSeq, M::NONE));
        }
        // not a `CSI u` key event, parse it as a legacy sequence
        // csi[0] is '[', csi[1] is seq2 (passed directly below),
        // so push back the remainder (csi[2..]) for the legacy parser
        self.pushback.extend(csi[2..].iter().copied());
        if let Some(c) = trailing {
            let mut buf = [0u8; 4];
            self.pushback.extend(c.encode_utf8(&mut buf).bytes());
        }
        self.escape_csi_legacy(seq2)
    }

    /// Handle \E[ <seq2:digit> escape sequences
    #[expect(clippy::cognitive_complexity)]
    fn extended_escape(&mut self, seq2: char) -> Result<KeyEvent> {
        let seq3 = self.next_char()?;
        if seq3 == '~' {
            Ok(match seq2 {
                '1' | RXVT_HOME => E(K::Home, M::NONE), // tmux, xrvt
                INSERT => E(K::Insert, M::NONE),
                DELETE => E(K::Delete, M::NONE),
                '4' | RXVT_END => E(K::End, M::NONE), // tmux, xrvt
                PAGE_UP => E(K::PageUp, M::NONE),
                PAGE_DOWN => E(K::PageDown, M::NONE),
                _ => {
                    debug!(target: "rustyline",
                           "unsupported esc sequence: \\E[{seq2}~");
                    E(K::UnknownEscSeq, M::NONE)
                }
            })
        } else if seq3.is_ascii_digit() {
            let seq4 = self.next_char()?;
            if seq4 == '~' {
                Ok(match (seq2, seq3) {
                    ('1', '1') => E(K::F(1), M::NONE),  // rxvt-unicode
                    ('1', '2') => E(K::F(2), M::NONE),  // rxvt-unicode
                    ('1', '3') => E(K::F(3), M::NONE),  // rxvt-unicode
                    ('1', '4') => E(K::F(4), M::NONE),  // rxvt-unicode
                    ('1', '5') => E(K::F(5), M::NONE),  // kf5
                    ('1', '7') => E(K::F(6), M::NONE),  // kf6
                    ('1', '8') => E(K::F(7), M::NONE),  // kf7
                    ('1', '9') => E(K::F(8), M::NONE),  // kf8
                    ('2', '0') => E(K::F(9), M::NONE),  // kf9
                    ('2', '1') => E(K::F(10), M::NONE), // kf10
                    ('2', '3') => E(K::F(11), M::NONE), // kf11
                    ('2', '4') => E(K::F(12), M::NONE), // kf12
                    //('6', '2') => KeyCode::ScrollUp,
                    //('6', '3') => KeyCode::ScrollDown,
                    _ => {
                        debug!(target: "rustyline",
                               "unsupported esc sequence: \\E[{seq2}{seq3}~");
                        E(K::UnknownEscSeq, M::NONE)
                    }
                })
            } else if seq4 == ';' {
                let seq5 = self.next_char()?;
                if seq5.is_ascii_digit() {
                    let seq6 = self.next_char()?;
                    if seq6.is_ascii_digit() {
                        self.next_char()?; // 'R' expected
                        Ok(E(K::UnknownEscSeq, M::NONE))
                    } else if seq6 == 'R' {
                        Ok(E(K::UnknownEscSeq, M::NONE))
                    } else if seq6 == '~' {
                        Ok(match (seq2, seq3, seq5) {
                            ('1', '5', CTRL) => E(K::F(5), M::CTRL),
                            //('1', '5', '6') => E(K::F(17), M::CTRL),
                            ('1', '7', CTRL) => E(K::F(6), M::CTRL),
                            //('1', '7', '6') => E(K::F(18), M::CTRL),
                            ('1', '8', CTRL) => E(K::F(7), M::CTRL),
                            ('1', '9', CTRL) => E(K::F(8), M::CTRL),
                            //('1', '9', '6') => E(K::F(19), M::CTRL),
                            ('2', '0', CTRL) => E(K::F(9), M::CTRL),
                            //('2', '0', '6') => E(K::F(21), M::CTRL),
                            ('2', '1', CTRL) => E(K::F(10), M::CTRL),
                            //('2', '1', '6') => E(K::F(22), M::CTRL),
                            ('2', '3', CTRL) => E(K::F(11), M::CTRL),
                            //('2', '3', '6') => E(K::F(23), M::CTRL),
                            ('2', '4', CTRL) => E(K::F(12), M::CTRL),
                            //('2', '4', '6') => E(K::F(24), M::CTRL),
                            _ => {
                                debug!(target: "rustyline",
                                       "unsupported esc sequence: \\E[{seq2}{seq3};{seq5}~");
                                E(K::UnknownEscSeq, M::NONE)
                            }
                        })
                    } else {
                        debug!(target: "rustyline",
                               "unsupported esc sequence: \\E[{seq2}{seq3};{seq5}{seq6}");
                        Ok(E(K::UnknownEscSeq, M::NONE))
                    }
                } else {
                    debug!(target: "rustyline",
                           "unsupported esc sequence: \\E[{seq2}{seq3};{seq5:?}");
                    Ok(E(K::UnknownEscSeq, M::NONE))
                }
            } else if seq4.is_ascii_digit() {
                let seq5 = self.next_char()?;
                if seq5 == '~' {
                    Ok(match (seq2, seq3, seq4) {
                        ('2', '0', '0') => E(K::BracketedPasteStart, M::NONE),
                        ('2', '0', '1') => E(K::BracketedPasteEnd, M::NONE),
                        _ => {
                            debug!(target: "rustyline",
                                   "unsupported esc sequence: \\E[{seq2}{seq3}{seq4}~");
                            E(K::UnknownEscSeq, M::NONE)
                        }
                    })
                } else {
                    debug!(target: "rustyline",
                           "unsupported esc sequence: \\E[{seq2}{seq3}{seq4}{seq5}");
                    Ok(E(K::UnknownEscSeq, M::NONE))
                }
            } else {
                debug!(target: "rustyline",
                       "unsupported esc sequence: \\E[{seq2}{seq3}{seq4:?}");
                Ok(E(K::UnknownEscSeq, M::NONE))
            }
        } else if seq3 == ';' {
            let seq4 = self.next_char()?;
            if seq4.is_ascii_digit() {
                let seq5 = self.next_char()?;
                if seq5.is_ascii_digit() {
                    self.next_char()?; // 'R' expected
                    //
                    //('1', '0', UP) => E(K::, M::), // Alt + Shift + Up
                    Ok(E(K::UnknownEscSeq, M::NONE))
                } else if seq2 == '1' {
                    Ok(match (seq4, seq5) {
                        (SHIFT, UP) => E(K::Up, M::SHIFT),     // ~ key_sr
                        (SHIFT, DOWN) => E(K::Down, M::SHIFT), // ~ key_sf
                        (SHIFT, RIGHT) => E(K::Right, M::SHIFT),
                        (SHIFT, LEFT) => E(K::Left, M::SHIFT),
                        (SHIFT, END) => E(K::End, M::SHIFT), // kEND
                        (SHIFT, HOME) => E(K::Home, M::SHIFT), // kHOM
                        //('2', 'P') => E(K::F(13), M::NONE),
                        //('2', 'Q') => E(K::F(14), M::NONE),
                        //('2', 'S') => E(K::F(16), M::NONE),
                        (ALT, UP) => E(K::Up, M::ALT),
                        (ALT, DOWN) => E(K::Down, M::ALT),
                        (ALT, RIGHT) => E(K::Right, M::ALT),
                        (ALT, LEFT) => E(K::Left, M::ALT),
                        (ALT, END) => E(K::End, M::ALT),
                        (ALT, HOME) => E(K::Home, M::ALT),
                        (ALT_SHIFT, UP) => E(K::Up, M::ALT_SHIFT),
                        (ALT_SHIFT, DOWN) => E(K::Down, M::ALT_SHIFT),
                        (ALT_SHIFT, RIGHT) => E(K::Right, M::ALT_SHIFT),
                        (ALT_SHIFT, LEFT) => E(K::Left, M::ALT_SHIFT),
                        (ALT_SHIFT, END) => E(K::End, M::ALT_SHIFT),
                        (ALT_SHIFT, HOME) => E(K::Home, M::ALT_SHIFT),
                        (CTRL, UP) => E(K::Up, M::CTRL),
                        (CTRL, DOWN) => E(K::Down, M::CTRL),
                        (CTRL, RIGHT) => E(K::Right, M::CTRL),
                        (CTRL, LEFT) => E(K::Left, M::CTRL),
                        (CTRL, END) => E(K::End, M::CTRL),
                        (CTRL, HOME) => E(K::Home, M::CTRL),
                        (CTRL, 'P') => E(K::F(1), M::CTRL),
                        (CTRL, 'Q') => E(K::F(2), M::CTRL),
                        (CTRL, 'S') => E(K::F(4), M::CTRL),
                        (CTRL, 'p') => E(K::Char('0'), M::CTRL),
                        (CTRL, 'q') => E(K::Char('1'), M::CTRL),
                        (CTRL, 'r') => E(K::Char('2'), M::CTRL),
                        (CTRL, 's') => E(K::Char('3'), M::CTRL),
                        (CTRL, 't') => E(K::Char('4'), M::CTRL),
                        (CTRL, 'u') => E(K::Char('5'), M::CTRL),
                        (CTRL, 'v') => E(K::Char('6'), M::CTRL),
                        (CTRL, 'w') => E(K::Char('7'), M::CTRL),
                        (CTRL, 'x') => E(K::Char('8'), M::CTRL),
                        (CTRL, 'y') => E(K::Char('9'), M::CTRL),
                        (CTRL_SHIFT, UP) => E(K::Up, M::CTRL_SHIFT),
                        (CTRL_SHIFT, DOWN) => E(K::Down, M::CTRL_SHIFT),
                        (CTRL_SHIFT, RIGHT) => E(K::Right, M::CTRL_SHIFT),
                        (CTRL_SHIFT, LEFT) => E(K::Left, M::CTRL_SHIFT),
                        (CTRL_SHIFT, END) => E(K::End, M::CTRL_SHIFT),
                        (CTRL_SHIFT, HOME) => E(K::Home, M::CTRL_SHIFT),
                        //('6', 'P') => E(K::F(13), M::CTRL),
                        //('6', 'Q') => E(K::F(14), M::CTRL),
                        //('6', 'S') => E(K::F(16), M::CTRL),
                        (CTRL_SHIFT, 'p') => E(K::Char('0'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'q') => E(K::Char('1'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'r') => E(K::Char('2'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 's') => E(K::Char('3'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 't') => E(K::Char('4'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'u') => E(K::Char('5'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'v') => E(K::Char('6'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'w') => E(K::Char('7'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'x') => E(K::Char('8'), M::CTRL_SHIFT),
                        (CTRL_SHIFT, 'y') => E(K::Char('9'), M::CTRL_SHIFT),
                        (CTRL_ALT, UP) => E(K::Up, M::CTRL_ALT),
                        (CTRL_ALT, DOWN) => E(K::Down, M::CTRL_ALT),
                        (CTRL_ALT, RIGHT) => E(K::Right, M::CTRL_ALT),
                        (CTRL_ALT, LEFT) => E(K::Left, M::CTRL_ALT),
                        (CTRL_ALT, END) => E(K::End, M::CTRL_ALT),
                        (CTRL_ALT, HOME) => E(K::Home, M::CTRL_ALT),
                        (CTRL_ALT, 'p') => E(K::Char('0'), M::CTRL_ALT),
                        (CTRL_ALT, 'q') => E(K::Char('1'), M::CTRL_ALT),
                        (CTRL_ALT, 'r') => E(K::Char('2'), M::CTRL_ALT),
                        (CTRL_ALT, 's') => E(K::Char('3'), M::CTRL_ALT),
                        (CTRL_ALT, 't') => E(K::Char('4'), M::CTRL_ALT),
                        (CTRL_ALT, 'u') => E(K::Char('5'), M::CTRL_ALT),
                        (CTRL_ALT, 'v') => E(K::Char('6'), M::CTRL_ALT),
                        (CTRL_ALT, 'w') => E(K::Char('7'), M::CTRL_ALT),
                        (CTRL_ALT, 'x') => E(K::Char('8'), M::CTRL_ALT),
                        (CTRL_ALT, 'y') => E(K::Char('9'), M::CTRL_ALT),
                        (CTRL_ALT_SHIFT, UP) => E(K::Up, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, DOWN) => E(K::Down, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, RIGHT) => E(K::Right, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, LEFT) => E(K::Left, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, END) => E(K::End, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, HOME) => E(K::Home, M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'p') => E(K::Char('0'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'q') => E(K::Char('1'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'r') => E(K::Char('2'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 's') => E(K::Char('3'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 't') => E(K::Char('4'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'u') => E(K::Char('5'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'v') => E(K::Char('6'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'w') => E(K::Char('7'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'x') => E(K::Char('8'), M::CTRL_ALT_SHIFT),
                        (CTRL_ALT_SHIFT, 'y') => E(K::Char('9'), M::CTRL_ALT_SHIFT),
                        // Meta + arrow on (some?) Macs when using iTerm defaults
                        ('9', UP) => E(K::Up, M::ALT),
                        ('9', DOWN) => E(K::Down, M::ALT),
                        ('9', RIGHT) => E(K::Right, M::ALT),
                        ('9', LEFT) => E(K::Left, M::ALT),
                        _ => {
                            debug!(target: "rustyline",
                                   "unsupported esc sequence: \\E[1;{seq4}{seq5:?}");
                            E(K::UnknownEscSeq, M::NONE)
                        }
                    })
                } else if seq5 == '~' {
                    Ok(match (seq2, seq4) {
                        (INSERT, SHIFT) => E(K::Insert, M::SHIFT),
                        (INSERT, ALT) => E(K::Insert, M::ALT),
                        (INSERT, ALT_SHIFT) => E(K::Insert, M::ALT_SHIFT),
                        (INSERT, CTRL) => E(K::Insert, M::CTRL),
                        (INSERT, CTRL_SHIFT) => E(K::Insert, M::CTRL_SHIFT),
                        (INSERT, CTRL_ALT) => E(K::Insert, M::CTRL_ALT),
                        (INSERT, CTRL_ALT_SHIFT) => E(K::Insert, M::CTRL_ALT_SHIFT),
                        (DELETE, SHIFT) => E(K::Delete, M::SHIFT),
                        (DELETE, ALT) => E(K::Delete, M::ALT),
                        (DELETE, ALT_SHIFT) => E(K::Delete, M::ALT_SHIFT),
                        (DELETE, CTRL) => E(K::Delete, M::CTRL),
                        (DELETE, CTRL_SHIFT) => E(K::Delete, M::CTRL_SHIFT),
                        (DELETE, CTRL_ALT) => E(K::Delete, M::CTRL_ALT),
                        (DELETE, CTRL_ALT_SHIFT) => E(K::Delete, M::CTRL_ALT_SHIFT),
                        (PAGE_UP, SHIFT) => E(K::PageUp, M::SHIFT),
                        (PAGE_UP, ALT) => E(K::PageUp, M::ALT),
                        (PAGE_UP, ALT_SHIFT) => E(K::PageUp, M::ALT_SHIFT),
                        (PAGE_UP, CTRL) => E(K::PageUp, M::CTRL),
                        (PAGE_UP, CTRL_SHIFT) => E(K::PageUp, M::CTRL_SHIFT),
                        (PAGE_UP, CTRL_ALT) => E(K::PageUp, M::CTRL_ALT),
                        (PAGE_UP, CTRL_ALT_SHIFT) => E(K::PageUp, M::CTRL_ALT_SHIFT),
                        (PAGE_DOWN, SHIFT) => E(K::PageDown, M::SHIFT),
                        (PAGE_DOWN, ALT) => E(K::PageDown, M::ALT),
                        (PAGE_DOWN, ALT_SHIFT) => E(K::PageDown, M::ALT_SHIFT),
                        (PAGE_DOWN, CTRL) => E(K::PageDown, M::CTRL),
                        (PAGE_DOWN, CTRL_SHIFT) => E(K::PageDown, M::CTRL_SHIFT),
                        (PAGE_DOWN, CTRL_ALT) => E(K::PageDown, M::CTRL_ALT),
                        (PAGE_DOWN, CTRL_ALT_SHIFT) => E(K::PageDown, M::CTRL_ALT_SHIFT),
                        _ => {
                            debug!(target: "rustyline",
                                   "unsupported esc sequence: \\E[{seq2};{seq4:?}~");
                            E(K::UnknownEscSeq, M::NONE)
                        }
                    })
                } else {
                    debug!(target: "rustyline",
                           "unsupported esc sequence: \\E[{seq2};{seq4}{seq5:?}");
                    Ok(E(K::UnknownEscSeq, M::NONE))
                }
            } else {
                debug!(target: "rustyline",
                       "unsupported esc sequence: \\E[{seq2};{seq4:?}");
                Ok(E(K::UnknownEscSeq, M::NONE))
            }
        } else {
            Ok(match (seq2, seq3) {
                (DELETE, RXVT_CTRL) => E(K::Delete, M::CTRL),
                (DELETE, RXVT_CTRL_SHIFT) => E(K::Delete, M::CTRL_SHIFT),
                (CTRL, UP) => E(K::Up, M::CTRL),
                (CTRL, DOWN) => E(K::Down, M::CTRL),
                (CTRL, RIGHT) => E(K::Right, M::CTRL),
                (CTRL, LEFT) => E(K::Left, M::CTRL),
                (PAGE_UP, RXVT_CTRL) => E(K::PageUp, M::CTRL),
                (PAGE_UP, RXVT_SHIFT) => E(K::PageUp, M::SHIFT),
                (PAGE_UP, RXVT_CTRL_SHIFT) => E(K::PageUp, M::CTRL_SHIFT),
                (PAGE_DOWN, RXVT_CTRL) => E(K::PageDown, M::CTRL),
                (PAGE_DOWN, RXVT_SHIFT) => E(K::PageDown, M::SHIFT),
                (PAGE_DOWN, RXVT_CTRL_SHIFT) => E(K::PageDown, M::CTRL_SHIFT),
                (RXVT_HOME, RXVT_CTRL) => E(K::Home, M::CTRL),
                (RXVT_HOME, RXVT_SHIFT) => E(K::Home, M::SHIFT),
                (RXVT_HOME, RXVT_CTRL_SHIFT) => E(K::Home, M::CTRL_SHIFT),
                (RXVT_END, RXVT_CTRL) => E(K::End, M::CTRL), // kEND5 or kel
                (RXVT_END, RXVT_SHIFT) => E(K::End, M::SHIFT),
                (RXVT_END, RXVT_CTRL_SHIFT) => E(K::End, M::CTRL_SHIFT),
                _ => {
                    debug!(target: "rustyline",
                           "unsupported esc sequence: \\E[{seq2}{seq3:?}");
                    E(K::UnknownEscSeq, M::NONE)
                }
            })
        }
    }

    /// Handle \EO <seq2> escape sequences
    fn escape_o(&mut self) -> Result<KeyEvent> {
        let seq2 = self.next_char()?;
        Ok(match seq2 {
            UP => E(K::Up, M::NONE),
            DOWN => E(K::Down, M::NONE),
            RIGHT => E(K::Right, M::NONE),
            LEFT => E(K::Left, M::NONE),
            //'E' => E(K::, M::),// key_b2, kb2
            END => E(K::End, M::NONE),   // kend
            HOME => E(K::Home, M::NONE), // khome
            'M' => E::ENTER,             // kent
            'P' => E(K::F(1), M::NONE),  // kf1
            'Q' => E(K::F(2), M::NONE),  // kf2
            'R' => E(K::F(3), M::NONE),  // kf3
            'S' => E(K::F(4), M::NONE),  // kf4
            'a' => E(K::Up, M::CTRL),
            'b' => E(K::Down, M::CTRL),
            'c' => E(K::Right, M::CTRL), // rxvt
            'd' => E(K::Left, M::CTRL),  // rxvt
            'l' => E(K::F(8), M::NONE),
            't' => E(K::F(5), M::NONE),  // kf5 or kb1
            'u' => E(K::F(6), M::NONE),  // kf6 or kb2
            'v' => E(K::F(7), M::NONE),  // kf7 or kb3
            'w' => E(K::F(9), M::NONE),  // kf9 or ka1
            'x' => E(K::F(10), M::NONE), // kf10 or ka2
            _ => {
                debug!(target: "rustyline", "unsupported esc sequence: \\EO{seq2:?}");
                E(K::UnknownEscSeq, M::NONE)
            }
        })
    }

    fn poll(&mut self, timeout: PollTimeout) -> Result<bool> {
        #[cfg(feature = "kitty-keyboard-protocol")]
        let n = self.tty_in.buffer().len() + self.pushback.len();
        #[cfg(not(feature = "kitty-keyboard-protocol"))]
        let n = self.tty_in.buffer().len();
        if n > 0 {
            return Ok(true);
        }
        #[cfg(target_os = "macos")]
        if self.is_dev_tty {
            // poll doesn't work for /dev/tty on MacOS but select does
            return Ok(match self.select(Some(timeout), false /* ignored */)? {
                Event::Timeout(true) => false,
                _ => true,
            });
        }
        debug!(target: "rustyline", "poll with: {timeout:?}");
        let mut fds = [poll::PollFd::new(self.as_fd(), PollFlags::POLLIN)];
        let r = poll::poll(&mut fds, timeout);
        debug!(target: "rustyline", "poll returns: {r:?}");
        match r {
            Ok(n) => Ok(n != 0),
            Err(Errno::EINTR) => {
                if let Some(signal) = self.tty_in.get_ref().sig()? {
                    Err(ReadlineError::Signal(signal))
                } else {
                    Ok(false) // Ignore EINTR while polling
                }
            }
            Err(e) => Err(e.into()),
        }
    }

    // timeout is used only with /dev/tty on MacOs
    fn select(&mut self, timeout: Option<PollTimeout>, single_esc_abort: bool) -> Result<Event> {
        let tty_in = self.as_fd();
        let sig_pipe = self.tty_in.get_ref().sig_fd();
        let pipe_reader = if timeout.is_some() {
            None
        } else {
            self.pipe_reader
                .as_ref()
                .map(|pr| pr.lock().unwrap().0.as_raw_fd())
                .map(|fd| unsafe { BorrowedFd::borrow_raw(fd) })
        };
        loop {
            let mut readfds = FdSet::new();
            if let Some(sig_pipe) = sig_pipe {
                readfds.insert(sig_pipe);
            }
            readfds.insert(tty_in);
            if let Some(pipe_reader) = pipe_reader {
                readfds.insert(pipe_reader);
            }
            let mut timeout = match timeout {
                Some(pt) => pt
                    .as_millis()
                    .map(|ms| nix::sys::time::TimeVal::milliseconds(i64::from(ms))),
                None => None,
            };
            if let Err(err) = select::select(None, Some(&mut readfds), None, None, timeout.as_mut())
            {
                if err == Errno::EINTR {
                    if let Some(signal) = self.tty_in.get_ref().sig()? {
                        return Err(ReadlineError::Signal(signal));
                    }
                    continue;
                }
                return Err(err.into());
            }
            if sig_pipe.is_some_and(|fd| readfds.contains(fd)) {
                if let Some(signal) = self.tty_in.get_ref().sig()? {
                    return Err(ReadlineError::Signal(signal));
                }
            } else if readfds.contains(tty_in) {
                #[cfg(target_os = "macos")]
                if timeout.is_some() {
                    return Ok(Event::Timeout(false));
                }
                // prefer user input over external print
                return self.next_key(single_esc_abort).map(Event::KeyPress);
            } else if timeout.is_some() {
                cfg_select! {
                    target_os = "macos" => {
                        return Ok(Event::Timeout(true));
                    }
                    _ => unreachable!(),
                }
            } else if let Some(ref pipe_reader) = self.pipe_reader {
                let mut guard = pipe_reader.lock().unwrap();
                let mut buf = [0; 1];
                guard.0.read_exact(&mut buf)?;
                if let Ok(msg) = guard.1.try_recv() {
                    return Ok(Event::ExternalPrint(msg));
                }
            }
        }
    }
}

impl RawReader for PosixRawReader {
    type Buffer = PosixBuffer;

    fn wait_for_input(&mut self, single_esc_abort: bool) -> Result<Event> {
        #[cfg(feature = "kitty-keyboard-protocol")]
        let has_input = !self.tty_in.buffer().is_empty() || !self.pushback.is_empty();
        #[cfg(not(feature = "kitty-keyboard-protocol"))]
        let has_input = !self.tty_in.buffer().is_empty();
        if has_input {
            return self.next_key(single_esc_abort).map(Event::KeyPress);
        }
        cfg_select! {
            feature = "signal-hook" => self.select(None, single_esc_abort),
            _ => match self.pipe_reader {
                Some(_) => self.select(None, single_esc_abort),
                _ => self.next_key(single_esc_abort).map(Event::KeyPress),
            },
        }
    }

    fn next_key(&mut self, single_esc_abort: bool) -> Result<KeyEvent> {
        let c = self.next_char()?;

        let mut key = KeyEvent::new(c, M::NONE);
        if key == E::ESC {
            if !self.tty_in.buffer().is_empty() {
                debug!(target: "rustyline", "read buffer {:?}", self.tty_in.buffer());
            }
            let timeout_ms = if single_esc_abort && self.timeout_ms.is_none() {
                PollTimeout::ZERO
            } else {
                self.timeout_ms
            };
            match self.poll(timeout_ms) {
                Ok(false) => {
                    // single escape
                }
                Ok(_) => {
                    // escape sequence
                    key = self.escape_sequence()?;
                }
                // Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
        debug!(target: "rustyline", "c: {c:?} => key: {key:?}");
        Ok(key)
    }

    fn next_char(&mut self) -> Result<char> {
        let mut buf = [0; 1];
        let mut receiver = Utf8 {
            c: None,
            valid: true,
        };
        loop {
            let b = {
                #[cfg(feature = "kitty-keyboard-protocol")]
                {
                    if let Some(first) = self.pushback.pop_front() {
                        first
                    } else {
                        let n = self.tty_in.read(&mut buf)?;
                        if n == 0 {
                            return Err(ReadlineError::Eof);
                        }
                        buf[0]
                    }
                }
                #[cfg(not(feature = "kitty-keyboard-protocol"))]
                {
                    let n = self.tty_in.read(&mut buf)?;
                    if n == 0 {
                        return Err(ReadlineError::Eof);
                    }
                    buf[0]
                }
            };
            self.parser.advance(&mut receiver, b);
            if !receiver.valid {
                return Err(ReadlineError::from(ErrorKind::InvalidData));
            } else if let Some(c) = receiver.c.take() {
                return Ok(c);
            }
        }
    }

    fn read_pasted_text(&mut self) -> Result<String> {
        let mut buffer = String::new();
        loop {
            match self.next_char()? {
                '\x1b' => {
                    let key = self.escape_sequence()?;
                    if key == E(K::BracketedPasteEnd, M::NONE) {
                        break;
                    }
                    continue; // TODO validate
                }
                c => buffer.push(c),
            }
        }
        let buffer = buffer.replace("\r\n", "\n");
        let buffer = buffer.replace('\r', "\n");
        Ok(buffer)
    }

    fn find_binding(&self, key: &KeyEvent) -> Option<Cmd> {
        let cmd = self.key_map.get(key).cloned();
        if let Some(ref cmd) = cmd {
            debug!(target: "rustyline", "terminal key binding: {key:?} => {cmd:?}");
        }
        cmd
    }

    #[cfg(any(not(feature = "buffer-redux"), test))]
    fn unbuffer(self) -> Option<PosixBuffer> {
        None
    }

    #[cfg(all(feature = "buffer-redux", not(test)))]
    fn unbuffer(self) -> Option<PosixBuffer> {
        let (_, buffer) = self.tty_in.into_inner_with_buffer();
        Some(buffer)
    }
}

impl Receiver for Utf8 {
    /// Called whenever a code point is parsed successfully
    fn codepoint(&mut self, c: char) {
        self.c = Some(c);
        self.valid = true;
    }

    /// Called when an invalid sequence is detected
    fn invalid_sequence(&mut self) {
        self.c = None;
        self.valid = false;
    }
}

/// Console output writer
pub struct PosixRenderer {
    out: AltFd,
    cols: Unit, // Number of columns in terminal
    buffer: String,
    tab_stop: Unit,
    colors_enabled: bool,
    enable_synchronized_output: bool,
    grapheme_cluster_mode: GraphemeClusterMode,
    bell_style: BellStyle,
    /// 0 when BSU is first used or after last ESU
    synchronized_update: usize,
}

impl PosixRenderer {
    fn new(
        out: AltFd,
        tab_stop: Unit,
        colors_enabled: bool,
        enable_synchronized_output: bool,
        grapheme_cluster_mode: GraphemeClusterMode,
        bell_style: BellStyle,
    ) -> Self {
        let (cols, _) = get_win_size(out);
        Self {
            out,
            cols,
            buffer: String::with_capacity(1024),
            tab_stop,
            colors_enabled,
            enable_synchronized_output,
            grapheme_cluster_mode,
            bell_style,
            synchronized_update: 0,
        }
    }

    fn clear_old_rows(&mut self, layout: &Layout) {
        use std::fmt::Write as _;
        let current_row = layout.cursor.row;
        let old_rows = layout.end.row;
        // old_rows < cursor_row if the prompt spans multiple lines and if
        // this is the default State.
        let cursor_row_movement = old_rows.saturating_sub(current_row);
        // move the cursor down as required
        if cursor_row_movement > 0 {
            write!(self.buffer, "\x1b[{cursor_row_movement}B").unwrap();
        }
        // clear old rows
        for _ in 0..old_rows {
            self.buffer.push_str("\r\x1b[K\x1b[A");
        }
        // clear the line
        self.buffer.push_str("\r\x1b[K");
    }
}

impl Renderer for PosixRenderer {
    type Reader = PosixRawReader;

    fn move_cursor(&mut self, old: Position, new: Position) -> Result<()> {
        use std::fmt::Write as _;
        self.buffer.clear();
        let row_ordering = new.row.cmp(&old.row);
        if row_ordering == cmp::Ordering::Greater {
            // move down
            let row_shift = new.row - old.row;
            if row_shift == 1 {
                self.buffer.push_str("\x1b[B");
            } else {
                write!(self.buffer, "\x1b[{row_shift}B")?;
            }
        } else if row_ordering == cmp::Ordering::Less {
            // move up
            let row_shift = old.row - new.row;
            if row_shift == 1 {
                self.buffer.push_str("\x1b[A");
            } else {
                write!(self.buffer, "\x1b[{row_shift}A")?;
            }
        }
        let col_ordering = new.col.cmp(&old.col);
        if col_ordering == cmp::Ordering::Greater {
            // move right
            let col_shift = new.col - old.col;
            if col_shift == 1 {
                self.buffer.push_str("\x1b[C");
            } else {
                write!(self.buffer, "\x1b[{col_shift}C")?;
            }
        } else if col_ordering == cmp::Ordering::Less {
            // move left
            let col_shift = old.col - new.col;
            if col_shift == 1 {
                self.buffer.push_str("\x1b[D");
            } else {
                write!(self.buffer, "\x1b[{col_shift}D")?;
            }
        }
        write_all(self.out, self.buffer.as_str())?;
        Ok(())
    }

    fn refresh_line<P: Prompt + ?Sized>(
        &mut self,
        prompt: &P,
        line: &LineBuffer,
        hint: Option<&str>,
        old_layout: Option<&Layout>,
        new_layout: &Layout,
        highlighter: Option<&dyn Highlighter>,
    ) -> Result<()> {
        use std::fmt::Write as _;
        self.begin_synchronized_update()?;
        self.buffer.clear();

        let default_prompt = new_layout.default_prompt;
        let cursor = new_layout.cursor;
        let end_pos = new_layout.end;

        if let Some(old_layout) = old_layout {
            self.clear_old_rows(old_layout);
        }

        if let Some(highlighter) = highlighter {
            // display the prompt
            self.buffer
                .push_str(&highlighter.highlight_prompt(prompt.styled(), default_prompt));
            // display the input line
            self.buffer
                .push_str(&highlighter.highlight(line, line.pos()));
        } else {
            // display the prompt
            self.buffer.push_str(prompt.raw());
            // display the input line
            self.buffer.push_str(line);
        }
        // display hint
        if let Some(hint) = hint {
            if let Some(highlighter) = highlighter {
                self.buffer.push_str(&highlighter.highlight_hint(hint));
            } else {
                self.buffer.push_str(hint);
            }
        }
        // we have to generate our own newline on line wrap
        if end_pos.col == 0
            && end_pos.row > 0
            && !hint.map_or_else(|| line.ends_with('\n'), |h| h.ends_with('\n'))
        {
            self.buffer.push('\n');
        }
        // position the cursor
        let new_cursor_row_movement = end_pos.row - cursor.row;
        // move the cursor up as required
        if new_cursor_row_movement > 0 {
            write!(self.buffer, "\x1b[{new_cursor_row_movement}A")?;
        }
        // position the cursor within the line
        if cursor.col > 0 {
            write!(self.buffer, "\r\x1b[{}C", cursor.col)?;
        } else {
            self.buffer.push('\r');
        }

        write_all(self.out, self.buffer.as_str())?;
        self.end_synchronized_update()?;
        Ok(())
    }

    fn write_and_flush(&mut self, buf: &str) -> Result<()> {
        write_all(self.out, buf)?;
        Ok(())
    }

    /// Control characters are treated as having zero width.
    /// Characters with 2 column width are correctly handled (not split).
    fn calculate_position(&self, s: &str, orig: Position) -> Position {
        let mut pos = orig;
        let mut esc_seq = 0;
        for c in s.graphemes(true) {
            if c == "\n" {
                pos.row += 1;
                pos.col = 0;
                continue;
            }
            let cw = if c == "\t" {
                self.tab_stop - (pos.col % self.tab_stop)
            } else {
                width(self.grapheme_cluster_mode, c, &mut esc_seq)
            };
            pos.col += cw;
            if pos.col > self.cols {
                pos.row += 1;
                pos.col = cw;
            }
        }
        if pos.col == self.cols {
            pos.col = 0;
            pos.row += 1;
        }
        pos
    }

    fn beep(&mut self) -> Result<()> {
        match self.bell_style {
            BellStyle::Audible => self.write_and_flush("\x07"),
            _ => Ok(()),
        }
    }

    /// Clear the screen. Used to handle ctrl+l
    fn clear_screen(&mut self) -> Result<()> {
        self.write_and_flush("\x1b[H\x1b[J")
    }

    fn clear_rows(&mut self, layout: &Layout) -> Result<()> {
        self.buffer.clear();
        self.clear_old_rows(layout);
        write_all(self.out, self.buffer.as_str())?;
        Ok(())
    }

    /// Clear from cursor to end of line. Used to optimize deletion at EOL
    fn clear_to_eol(&mut self) -> Result<()> {
        self.write_and_flush("\x1b[K")
    }

    /// Try to update the number of columns in the current terminal,
    fn update_size(&mut self) {
        let (cols, _) = get_win_size(self.out);
        self.cols = cols;
    }

    fn get_columns(&self) -> Unit {
        self.cols
    }

    /// Try to get the number of rows in the current terminal,
    /// or assume 24 if it fails.
    fn get_rows(&self) -> Unit {
        let (_, rows) = get_win_size(self.out);
        rows
    }

    fn colors_enabled(&self) -> bool {
        self.colors_enabled
    }

    fn grapheme_cluster_mode(&self) -> GraphemeClusterMode {
        self.grapheme_cluster_mode
    }

    fn move_cursor_at_leftmost(&mut self, rdr: &mut PosixRawReader) -> Result<()> {
        if rdr.poll(PollTimeout::ZERO)? {
            debug!(target: "rustyline", "cannot request cursor location");
            return Ok(());
        }
        /* Report cursor location */
        self.write_and_flush("\x1b[6n")?;
        /* Read the response: ESC [ rows ; cols R */
        if !rdr.poll(PollTimeout::from(100u8))?
            || rdr.next_char()? != '\x1b'
            || rdr.next_char()? != '['
            || read_digits_until(rdr, ';')?.is_none()
        {
            warn!(target: "rustyline", "cannot read initial cursor location");
            return Ok(());
        }
        let col = read_digits_until(rdr, 'R')?;
        debug!(target: "rustyline", "initial cursor location: {col:?}");
        if col != Some(1) {
            self.write_and_flush("\n")?;
        }
        Ok(())
    }

    fn begin_synchronized_update(&mut self) -> Result<()> {
        if self.enable_synchronized_output {
            if self.synchronized_update == 0 {
                self.write_and_flush(BEGIN_SYNCHRONIZED_UPDATE)?;
            }
            self.synchronized_update = self.synchronized_update.saturating_add(1);
        }
        Ok(())
    }

    fn end_synchronized_update(&mut self) -> Result<()> {
        if self.enable_synchronized_output {
            self.synchronized_update = self.synchronized_update.saturating_sub(1);
            if self.synchronized_update == 0 {
                self.write_and_flush(END_SYNCHRONIZED_UPDATE)?;
            }
        }
        Ok(())
    }
}

fn read_digits_until(rdr: &mut PosixRawReader, sep: char) -> Result<Option<u32>> {
    let mut num: u32 = 0;
    loop {
        match rdr.next_char()? {
            digit @ '0'..='9' => {
                num = num
                    .saturating_mul(10)
                    .saturating_add(digit.to_digit(10).unwrap());
                continue;
            }
            c if c == sep => break,
            _ => return Ok(None),
        }
    }
    Ok(Some(num))
}

fn write_all(fd: AltFd, buf: &str) -> nix::Result<()> {
    let mut bytes = buf.as_bytes();
    while !bytes.is_empty() {
        match write(fd, bytes) {
            Ok(0) => return Err(Errno::EIO),
            Ok(n) => bytes = &bytes[n..],
            Err(Errno::EINTR) => {}
            Err(r) => return Err(r),
        }
    }
    Ok(())
}

pub struct PosixCursorGuard(AltFd);

impl Drop for PosixCursorGuard {
    fn drop(&mut self) {
        let _ = set_cursor_visibility(self.0, true);
    }
}

fn set_cursor_visibility(fd: AltFd, visible: bool) -> Result<Option<PosixCursorGuard>> {
    write_all(fd, if visible { "\x1b[?25h" } else { "\x1b[?25l" })?;
    Ok(if visible {
        None
    } else {
        Some(PosixCursorGuard(fd))
    })
}

#[cfg(not(feature = "signal-hook"))]
static SIG_PIPE: AtomicI32 = AtomicI32::new(-1);
#[cfg(not(feature = "signal-hook"))]
extern "C" fn sig_handler(sig: libc::c_int) {
    let b = error::Signal::to_byte(sig);
    let fd = SIG_PIPE.load(Ordering::Relaxed);
    if fd == -1 {
        // might not be safe to use in signal handler:
        // warn!(target: "rustyline", "cannot notify signal {sig}");
    } else {
        let _ = write(AltFd(fd), &[b]);
    }
}

/// Output fd to turn the kitty keyboard protocol off in a signal handler.
/// `ISIG` stays on in raw mode, so the kernel stops the process on Ctrl+Z
/// before the editor can read the key (and disable the protocol); the shell
/// restores termios on `fg` but not the kitty capability, which would
/// otherwise leak into the next foreground program. Set while the protocol
/// is active, cleared when it is not.
#[cfg(all(not(feature = "signal-hook"), feature = "kitty-keyboard-protocol"))]
static KITTY_SIGTSTP_OUT: AtomicI32 = AtomicI32::new(-1);
/// Turn the kitty protocol off, reset to the default (stop) disposition, and
/// re-raise so the process is still stopped by the original SIGTSTP.
#[cfg(all(not(feature = "signal-hook"), feature = "kitty-keyboard-protocol"))]
extern "C" fn kitty_sigstop_handler(_sig: libc::c_int) {
    use nix::sys::signal::{kill, sigaction, SaFlags, SigAction, SigHandler, Signal};
    use nix::unistd::Pid;
    let fd = KITTY_SIGTSTP_OUT.load(Ordering::Relaxed);
    if fd != -1 {
        let _ = write(AltFd(fd), KITTY_DISABLE.as_bytes());
    }
    // Reset to the default action so the re-raise below stops the process
    // (`SA_NODEFER` keeps the signal unblocked during the reset).
    let sa = SigAction::new(
        SigHandler::SigDfl,
        SaFlags::SA_NODEFER,
        nix::sys::signal::SigSet::empty(),
    );
    unsafe {
        let _ = sigaction(Signal::SIGTSTP, &sa);
    }
    let _ = kill(Pid::from_raw(0), Signal::SIGTSTP);
}
/// Install the SIGTSTP handler so a stop disables the kitty protocol before
/// the process is suspended. Called on every `enable_raw_mode`; the matching
/// `disable_raw_mode` resets the disposition, so there is no state that
/// outlives a raw session.
#[cfg(all(not(feature = "signal-hook"), feature = "kitty-keyboard-protocol"))]
fn install_kitty_sigstop_handler(out: AltFd) {
    use nix::sys::signal::{sigaction, SaFlags, SigAction, SigHandler, Signal};
    KITTY_SIGTSTP_OUT.store(out.0, Ordering::Relaxed);
    let sa = SigAction::new(
        SigHandler::Handler(kitty_sigstop_handler),
        SaFlags::empty(),
        nix::sys::signal::SigSet::empty(),
    );
    unsafe {
        let _ = sigaction(Signal::SIGTSTP, &sa);
    }
}
/// Reset SIGTSTP to its default (stop) action and drop the fd, so a stop
/// no longer tries to disable the protocol. Pairs with
/// `install_kitty_sigstop_handler` on every `disable_raw_mode`.
#[cfg(all(not(feature = "signal-hook"), feature = "kitty-keyboard-protocol"))]
fn clear_kitty_sigstop_handler() {
    use nix::sys::signal::{sigaction, SaFlags, SigAction, SigHandler, Signal};
    KITTY_SIGTSTP_OUT.store(-1, Ordering::Relaxed);
    let sa = SigAction::new(SigHandler::SigDfl, SaFlags::empty(), nix::sys::signal::SigSet::empty());
    unsafe {
        let _ = sigaction(Signal::SIGTSTP, &sa);
    }
}

#[derive(Debug)]
struct Sig {
    pipe: UnixStream,
    #[cfg(not(feature = "signal-hook"))]
    original_sigint: nix::sys::signal::SigAction,
    #[cfg(not(feature = "signal-hook"))]
    original_sigwinch: nix::sys::signal::SigAction,
    #[cfg(feature = "signal-hook")]
    id: signal_hook::SigId,
}
impl Sig {
    fn install_sigwinch_handler() -> Result<Self> {
        let (pipe, pipe_write) = UnixStream::pair()?;
        pipe.set_nonblocking(true)?;
        cfg_select! {
            feature = "signal-hook" => {
                let id = signal_hook::low_level::pipe::register(libc::SIGWINCH, pipe_write)?;
                Ok(Self { pipe, id })
            }
            _ => {
                use nix::sys::signal;
                SIG_PIPE
                    .compare_exchange(
                        -1,
                        pipe_write.into_raw_fd(),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .expect("Previous `pipe_write` should have been closed");
                let sa = signal::SigAction::new(
                    signal::SigHandler::Handler(sig_handler),
                    signal::SaFlags::empty(),
                    signal::SigSet::empty(),
                );
                let original_sigint = unsafe { signal::sigaction(signal::SIGINT, &sa)? };
                let original_sigwinch = unsafe { signal::sigaction(signal::SIGWINCH, &sa)? };
                Ok(Self {
                    pipe,
                    original_sigint,
                    original_sigwinch,
                })
            }
        }
    }

    fn uninstall_sigwinch_handler(self) -> Result<()> {
        cfg_select! {
            feature = "signal-hook" => {
                signal_hook::low_level::unregister(self.id);
                close(self.pipe)?;
            }
            _ => {
                use nix::sys::signal;
                let _ = unsafe { signal::sigaction(signal::SIGINT, &self.original_sigint)? };
                let _ = unsafe { signal::sigaction(signal::SIGWINCH, &self.original_sigwinch)? };
                close(self.pipe)?;
                let fd = SIG_PIPE.swap(-1, Ordering::Relaxed);
                if fd == -1 {
                    warn!(target: "rustyline", "Invalid `pipe_write`");
                } else {
                    close(fd)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(not(test))]
pub type Terminal = PosixTerminal;

#[derive(Clone, Debug)]
pub struct PosixTerminal {
    unsupported: bool,
    tty_in: AltFd,
    is_in_a_tty: bool,
    tty_out: AltFd,
    is_out_a_tty: bool,
    close_on_drop: bool,
    raw_mode: Arc<AtomicBool>,
    // external print reader
    pipe_reader: Option<PipeReader>,
    // external print writer
    pipe_writer: Option<PipeWriter>,
    /// Kitty keyboard protocol detection state
    #[cfg(feature = "kitty-keyboard-protocol")]
    kitty: KittyDetection,
    /// Leftover bytes read while probing for kitty support (a trailing
    /// progressive-enhancement response, or a user keystroke that arrived
    /// during the probe). Consumed by the next reader's pushback so it is
    /// not lost.
    #[cfg(feature = "kitty-keyboard-protocol")]
    pending_probe: Vec<u8>,
}

impl PosixTerminal {
    fn colors_enabled(&self, config: &Config) -> bool {
        match config.color_mode() {
            ColorMode::Enabled => self.is_out_a_tty,
            ColorMode::Forced => true,
            ColorMode::Disabled => false,
        }
    }

    /// Check if the terminal supports the kitty keyboard protocol.
    ///
    /// As described in the protocol documentation, the terminal is asked for
    /// the current progressive enhancement status and for its primary device
    /// attributes: if the device attributes are answered without an answer
    /// for the progressive enhancement, the terminal does not support the
    /// protocol.
    ///
    /// Must be called while raw mode is enabled.
    /// Returns true if the terminal supports the protocol. A negative probe
    /// result is cached so the probe is not repeated on every read.
    #[cfg(feature = "kitty-keyboard-protocol")]
    fn check_kitty_support(&mut self) -> bool {
        match self.kitty {
            KittyDetection::Unsupported => false,
            KittyDetection::Confirmed => true,
            // not probed yet: try to probe
            KittyDetection::Off => {
                // do not probe if there is input pending (it would be
                // consumed while reading the response), probe again next time
                match poll::poll(
                    &mut [poll::PollFd::new(self.tty_in.as_fd(), PollFlags::POLLIN)],
                    PollTimeout::ZERO,
                ) {
                    Ok(0) => self.probe_kitty_support(),
                    _ => false,
                }
            }
        }
    }

    /// Probe the terminal once to determine whether it supports the kitty
    /// keyboard protocol.
    #[cfg(feature = "kitty-keyboard-protocol")]
    fn probe_kitty_support(&mut self) -> bool {
        let supported = if let Err(e) = write_all(self.tty_out, KITTY_PROBE) {
            debug!(target: "rustyline", "Cannot probe kitty keyboard protocol: {e}");
            false
        } else {
            match self.read_kitty_response() {
                Ok(supported) => supported,
                Err(e) => {
                    debug!(target: "rustyline", "kitty probe failed: {e}");
                    false
                }
            }
        };
        if !supported {
            self.kitty = KittyDetection::Unsupported;
        }
        supported
    }

    /// Read the terminal's response to the kitty probe.
    ///
    /// The probe asks for the primary device attributes (`\E[c`); a terminal
    /// that supports the protocol also answers for the progressive
    /// enhancement status (`\E[?u`). We scan the response byte by byte and
    /// stop as soon as the device-attributes response (`\E[?…c`) is complete,
    /// so the window during which user keystrokes could be read (and
    /// discarded) is kept to a single burst of reads. Any bytes read after
    /// the DA response — a trailing progressive-enhancement response, or a
    /// user keystroke that arrived in the same burst — are stored in
    /// `pending_probe` to be handed to the next reader, so they are not lost.
    ///
    /// Returns true if the terminal supports the protocol.
    #[cfg(feature = "kitty-keyboard-protocol")]
    fn read_kitty_response(&mut self) -> Result<bool> {
        // state of the in-progress response scan
        const S0: u8 = 0; // expecting ESC
        const S1: u8 = 1; // ESC, expecting '['
        const S2: u8 = 2; // ESC [ , expecting '?'
        const S3: u8 = 3; // ESC [ ? , reading params, expecting final byte
        const S4: u8 = 4; // DA response complete
        const ROUNDS: usize = 5; // 5 x 100 ms: give up if no response
        let mut state = S0;
        let mut found_pe = false;
        let mut leftover = Vec::new();
        let mut buffer = [0u8; 64];
        for _ in 0..ROUNDS {
            let mut fds = [poll::PollFd::new(self.tty_in.as_fd(), PollFlags::POLLIN)];
            match poll::poll(&mut fds, PollTimeout::from(KITTY_PROBE_TIMEOUT_MS)) {
                Ok(0) => break, // no (more) response
                Ok(_) => {
                    // read is EINTR-safe: retry on EINTR
                    let n = loop {
                        match read(self.tty_in, &mut buffer) {
                            Ok(n) => break n,
                            Err(Errno::EINTR) => continue,
                            Err(e) => return Err(e.into()),
                        }
                    };
                    if n == 0 {
                        break;
                    }
                    for &b in &buffer[..n] {
                        if state == S4 {
                            // DA response already complete; this byte is
                            // not part of the probe response
                            leftover.push(b);
                            continue;
                        }
                        match state {
                            S0 => {
                                if b == 0x1b {
                                    state = S1;
                                }
                            }
                            S1 => {
                                if b == b'[' {
                                    state = S2;
                                } else {
                                    state = S0;
                                }
                            }
                            S2 => {
                                if b == b'?' {
                                    state = S3;
                                } else {
                                    state = S0;
                                }
                            }
                            S3 => {
                                if b == b'u' {
                                    found_pe = true;
                                    state = S0;
                                } else if b == b'c' {
                                    state = S4;
                                } else if b.is_ascii_digit() || b == b';' {
                                    // stay in S3
                                } else {
                                    state = S0;
                                }
                            }
                            _ => {}
                        }
                    }
                    if state == S4 {
                        break; // got the DA response
                    }
                }
                Err(Errno::EINTR) => continue,
                Err(e) => return Err(e.into()),
            }
        }
        // any leftover bytes (trailing PE response or a keystroke) are not
        // part of the probe response; hand them to the next reader
        self.pending_probe = leftover;
        Ok(found_pe)
    }
}

impl Term for PosixTerminal {
    type Buffer = PosixBuffer;
    type CursorGuard = PosixCursorGuard;
    type ExternalPrinter = ExternalPrinter;
    type KeyMap = PosixKeyMap;
    type Mode = PosixMode;
    type Reader = PosixRawReader;
    type Writer = PosixRenderer;

    fn new(config: &Config) -> Result<Self> {
        let (tty_in, is_in_a_tty, tty_out, is_out_a_tty, close_on_drop) =
            if config.behavior() == Behavior::PreferTerm {
                let tty = OpenOptions::new().read(true).write(true).open("/dev/tty");
                if let Ok(tty) = tty {
                    let fd = AltFd(tty.into_raw_fd());
                    let is_a_tty = is_a_tty(fd); // TODO: useless ?
                    (fd, is_a_tty, fd, is_a_tty, true)
                } else {
                    let (i, o) = (AltFd(libc::STDIN_FILENO), AltFd(libc::STDOUT_FILENO));
                    (i, is_a_tty(i), o, is_a_tty(o), false)
                }
            } else {
                let (i, o) = (AltFd(libc::STDIN_FILENO), AltFd(libc::STDOUT_FILENO));
                (i, is_a_tty(i), o, is_a_tty(o), false)
            };
        let unsupported = super::is_unsupported_term();
        Ok(Self {
            unsupported,
            tty_in,
            is_in_a_tty,
            tty_out,
            is_out_a_tty,
            close_on_drop,
            raw_mode: Arc::new(AtomicBool::new(false)),
            pipe_reader: None,
            pipe_writer: None,
            #[cfg(feature = "kitty-keyboard-protocol")]
            kitty: KittyDetection::Off,
            #[cfg(feature = "kitty-keyboard-protocol")]
            pending_probe: Vec::new(),
        })
    }

    // Init checks:

    /// Check if current terminal can provide a rich line-editing user
    /// interface.
    fn is_unsupported(&self) -> bool {
        self.unsupported
    }

    fn is_input_tty(&self) -> bool {
        self.is_in_a_tty
    }

    fn is_output_tty(&self) -> bool {
        self.is_out_a_tty
    }

    // Interactive loop:

    fn enable_raw_mode(&mut self, c: &Config) -> Result<(Self::Mode, PosixKeyMap)> {
        use nix::errno::Errno::ENOTTY;
        if !self.is_in_a_tty {
            return Err(ENOTTY.into());
        }
        let (original_mode, key_map) = termios_::enable_raw_mode(self.tty_in, c.enable_signals())?;

        self.raw_mode.store(true, Ordering::SeqCst);
        // enable bracketed paste
        let out = if !c.enable_bracketed_paste() {
            None
        } else if let Err(e) = write_all(self.tty_out, BRACKETED_PASTE_ON) {
            debug!(target: "rustyline", "Cannot enable bracketed paste: {e}");
            None
        } else {
            Some(self.tty_out)
        };

        // when all ExternalPrinter are dropped there is no need to use `pipe_reader`
        if Arc::strong_count(&self.raw_mode) == 1 {
            self.pipe_writer = None;
            self.pipe_reader = None;
        }

        // enable the kitty keyboard protocol
        #[cfg(feature = "kitty-keyboard-protocol")]
        {
            // the protocol is active for this session if it was requested and
            // the terminal supports it and the enable write succeeded
            let enabled = c.kitty_keyboard()
                && self.check_kitty_support()
                && write_all(self.tty_out, KITTY_ENABLE).is_ok();
            self.kitty = if enabled {
                KittyDetection::Confirmed
            } else if let KittyDetection::Confirmed = self.kitty {
                // was enabled on the previous session
                KittyDetection::Off
            } else {
                // keep `Off` (not probed / probe deferred) or `Unsupported`
                // (cached probe result)
                self.kitty
            };
        }
        // output fd to restore the kitty keyboard protocol on. It is
        // independent of the bracketed-paste `out` (which is `None` when
        // bracketed paste is disabled); it is `Some` only when the protocol
        // was actually enabled this session.
        #[cfg(feature = "kitty-keyboard-protocol")]
        let kitty_out = if matches!(self.kitty, KittyDetection::Confirmed) {
            Some(self.tty_out)
        } else {
            None
        };
        // arm the one-shot SIGTSTP handler for the duration of this raw
        // session, so a stop disables the protocol before the process is
        // suspended (the shell restores termios on `fg`, not the protocol).
        #[cfg(all(not(feature = "signal-hook"), feature = "kitty-keyboard-protocol"))]
        if let Some(out) = kitty_out {
            install_kitty_sigstop_handler(out);
        }

        Ok((
            PosixMode {
                termios: original_mode,
                tty_in: self.tty_in,
                tty_out: out,
                raw_mode: self.raw_mode.clone(),
                #[cfg(feature = "kitty-keyboard-protocol")]
                kitty_out,
            },
            key_map,
        ))
    }

    /// Create a RAW reader
    fn create_reader(
        &mut self,
        buffer: Option<PosixBuffer>,
        config: &Config,
        key_map: PosixKeyMap,
    ) -> Result<PosixRawReader> {
        debug_assert!(!self.unsupported && self.is_in_a_tty);
        let sig = if self.is_out_a_tty {
            Some(Sig::install_sigwinch_handler()?)
        } else {
            None
        };
        // the kitty keyboard protocol is only active if it was enabled on
        // the last call to `enable_raw_mode`
        #[cfg(feature = "kitty-keyboard-protocol")]
        let kitty = self.kitty == KittyDetection::Confirmed;
        // leftover bytes from the kitty probe (a trailing progressive-
        // enhancement response or a keystroke read during the probe); feed
        // them to the reader so they are parsed as input, not lost
        #[cfg(feature = "kitty-keyboard-protocol")]
        let pending = std::mem::take(&mut self.pending_probe);
        Ok(PosixRawReader::new(
            self.tty_in,
            sig,
            buffer,
            config,
            key_map,
            self.pipe_reader.clone(),
            #[cfg(feature = "kitty-keyboard-protocol")]
            kitty,
            #[cfg(feature = "kitty-keyboard-protocol")]
            pending,
            #[cfg(target_os = "macos")]
            self.close_on_drop,
        ))
    }

    fn create_writer(&self, c: &Config) -> PosixRenderer {
        PosixRenderer::new(
            self.tty_out,
            Unit::from(c.tab_stop()),
            self.colors_enabled(c),
            c.enable_synchronized_output(),
            c.grapheme_cluster_mode(),
            c.bell_style(),
        )
    }

    fn writeln(&self) -> Result<()> {
        write_all(self.tty_out, "\n")?;
        Ok(())
    }

    fn create_external_printer(&mut self) -> Result<ExternalPrinter> {
        use nix::unistd::pipe;
        if let Some(ref writer) = self.pipe_writer {
            return Ok(ExternalPrinter {
                writer: writer.clone(),
                raw_mode: self.raw_mode.clone(),
                tty_out: self.tty_out,
            });
        }
        if self.unsupported || !self.is_input_tty() || !self.is_output_tty() {
            return Err(nix::Error::ENOTTY.into());
        }
        let (sender, receiver) = mpsc::sync_channel(1); // TODO validate: bound
        let (r, w) = pipe()?;
        let reader = Arc::new(Mutex::new((r.into(), receiver)));
        let writer = (Arc::new(Mutex::new(w.into())), sender);
        self.pipe_reader.replace(reader);
        self.pipe_writer.replace(writer.clone());
        Ok(ExternalPrinter {
            writer,
            raw_mode: self.raw_mode.clone(),
            tty_out: self.tty_out,
        })
    }

    fn set_cursor_visibility(&mut self, visible: bool) -> Result<Option<PosixCursorGuard>> {
        if self.is_out_a_tty {
            set_cursor_visibility(self.tty_out, visible)
        } else {
            Ok(None)
        }
    }
}

#[expect(unused_must_use)]
impl Drop for PosixTerminal {
    fn drop(&mut self) {
        if self.close_on_drop {
            close(self.tty_in);
            debug_assert_eq!(self.tty_in, self.tty_out);
        }
    }
}

#[derive(Debug)]
pub struct ExternalPrinter {
    writer: PipeWriter,
    raw_mode: Arc<AtomicBool>,
    tty_out: AltFd,
}

impl super::ExternalPrinter for ExternalPrinter {
    fn print(&mut self, msg: String) -> Result<()> {
        // write directly to stdout/stderr while not in raw mode
        if !self.raw_mode.load(Ordering::SeqCst) {
            write_all(self.tty_out, msg.as_str())?;
        } else {
            match self.writer.0.lock() {
                Ok(mut writer) => {
                    self.writer
                        .1
                        .send(msg)
                        .map_err(|_| io::Error::from(ErrorKind::Other))?; // FIXME
                    writer.write_all(b"m")?;
                    writer.flush()?;
                }
                _ => {
                    return Err(io::Error::from(ErrorKind::Other).into()); // FIXME
                }
            }
        }
        Ok(())
    }
}

#[cfg(not(test))]
pub fn suspend() -> Result<()> {
    use nix::sys::signal;
    use nix::unistd::Pid;
    // suspend the whole process group
    signal::kill(Pid::from_raw(0), signal::SIGTSTP)?;
    Ok(())
}

#[cfg(not(feature = "termios"))]
mod termios_ {
    use std::collections::HashMap;

    use nix::sys::termios::{self, SetArg, SpecialCharacterIndices as SCI, Termios};

    use super::{AltFd, PosixKeyMap};
    use crate::keys::{KeyEvent, Modifiers as M};
    use crate::{Cmd, Result};
    pub fn disable_raw_mode(tty_in: AltFd, termios: &Termios) -> Result<()> {
        Ok(termios::tcsetattr(tty_in, SetArg::TCSADRAIN, termios)?)
    }
    pub fn enable_raw_mode(tty_in: AltFd, enable_signals: bool) -> Result<(Termios, PosixKeyMap)> {
        use nix::sys::termios::{ControlFlags, InputFlags, LocalFlags};

        let original_mode = termios::tcgetattr(tty_in)?;
        let mut raw = original_mode.clone();

        // https://linux.die.net/man/3/termios
        // > The above symbolic subscript values are all different, except that VTIME,
        // > VMIN may have the same value as VEOL, VEOF, respectively.
        // > In noncanonical mode the special character meaning is replaced by the
        // > timeout meaning.
        // So we must read VEOF before writing VTIME
        let mut key_map: HashMap<KeyEvent, Cmd> = HashMap::with_capacity(4);
        map_key(&mut key_map, &raw, SCI::VEOF, "VEOF", Cmd::EndOfFile);
        map_key(&mut key_map, &raw, SCI::VINTR, "VINTR", Cmd::Interrupt);
        map_key(&mut key_map, &raw, SCI::VQUIT, "VQUIT", Cmd::Interrupt);
        map_key(&mut key_map, &raw, SCI::VSUSP, "VSUSP", Cmd::Suspend);

        // disable BREAK interrupt, CR to NL conversion on input,
        // input parity check, strip high bit (bit 8), output flow control
        raw.input_flags &= !(InputFlags::BRKINT
            | InputFlags::ICRNL
            | InputFlags::INPCK
            | InputFlags::ISTRIP
            | InputFlags::IXON);
        // we don't want raw output, it turns newlines into straight line feeds
        // disable all output processing
        // raw.c_oflag = raw.c_oflag & !(OutputFlags::OPOST);

        // character-size mark (8 bits)
        raw.control_flags |= ControlFlags::CS8;
        // disable echoing, canonical mode, extended input processing and signals
        raw.local_flags &=
            !(LocalFlags::ECHO | LocalFlags::ICANON | LocalFlags::IEXTEN | LocalFlags::ISIG);

        if enable_signals {
            raw.local_flags |= LocalFlags::ISIG;
        }

        raw.control_chars[SCI::VMIN as usize] = 1; // One character-at-a-time input
        raw.control_chars[SCI::VTIME as usize] = 0; // with blocking read

        termios::tcsetattr(tty_in, SetArg::TCSADRAIN, &raw)?;
        Ok((original_mode, key_map))
    }
    fn map_key(
        key_map: &mut HashMap<KeyEvent, Cmd>,
        raw: &Termios,
        index: SCI,
        name: &str,
        cmd: Cmd,
    ) {
        let cc = char::from(raw.control_chars[index as usize]);
        let key = KeyEvent::new(cc, M::NONE);
        log::debug!(target: "rustyline", "{name}: {key:?}");
        key_map.insert(key, cmd);
    }
}
#[cfg(feature = "termios")]
mod termios_ {
    use std::collections::HashMap;

    use termios::{self, Termios};

    use super::{AltFd, PosixKeyMap};
    use crate::keys::{KeyEvent, Modifiers as M};
    use crate::{Cmd, Result};
    pub fn disable_raw_mode(tty_in: AltFd, termios: &Termios) -> Result<()> {
        Ok(termios::tcsetattr(tty_in.0, termios::TCSADRAIN, termios)?)
    }
    pub fn enable_raw_mode(tty_in: AltFd, enable_signals: bool) -> Result<(Termios, PosixKeyMap)> {
        let original_mode = Termios::from_fd(tty_in.0)?;
        let mut raw = original_mode;

        // https://linux.die.net/man/3/termios
        // > The above symbolic subscript values are all different, except that VTIME,
        // > VMIN may have the same value as VEOL, VEOF, respectively.
        // > In noncanonical mode the special character meaning is replaced by the
        // > timeout meaning.
        // So we must read VEOF before writing VTIME
        let mut key_map: HashMap<KeyEvent, Cmd> = HashMap::with_capacity(4);
        map_key(&mut key_map, &raw, termios::VEOF, "VEOF", Cmd::EndOfFile);
        map_key(&mut key_map, &raw, termios::VINTR, "VINTR", Cmd::Interrupt);
        map_key(&mut key_map, &raw, termios::VQUIT, "VQUIT", Cmd::Interrupt);
        map_key(&mut key_map, &raw, termios::VSUSP, "VSUSP", Cmd::Suspend);

        // disable BREAK interrupt, CR to NL conversion on input,
        // input parity check, strip high bit (bit 8), output flow control
        raw.c_iflag &=
            !(termios::BRKINT | termios::ICRNL | termios::INPCK | termios::ISTRIP | termios::IXON);
        // we don't want raw output, it turns newlines into straight line feeds
        // disable all output processing
        // raw.c_oflag = raw.c_oflag & !(OutputFlags::OPOST);

        // character-size mark (8 bits)
        raw.c_cflag |= termios::CS8;
        // disable echoing, canonical mode, extended input processing and signals
        raw.c_lflag &= !(termios::ECHO | termios::ICANON | termios::IEXTEN | termios::ISIG);

        if enable_signals {
            raw.c_lflag |= termios::ISIG;
        }

        raw.c_cc[termios::VMIN] = 1; // One character-at-a-time input
        raw.c_cc[termios::VTIME] = 0; // with blocking read

        termios::tcsetattr(tty_in.0, termios::TCSADRAIN, &raw)?;
        Ok((original_mode, key_map))
    }
    fn map_key(
        key_map: &mut HashMap<KeyEvent, Cmd>,
        raw: &Termios,
        index: usize,
        name: &str,
        cmd: Cmd,
    ) {
        let cc = char::from(raw.c_cc[index]);
        let key = KeyEvent::new(cc, M::NONE);
        log::debug!(target: "rustyline", "{name}: {key:?}");
        key_map.insert(key, cmd);
    }
}

#[cfg(feature = "kitty-keyboard-protocol")]
mod kitty {
    //! Parsing of kitty keyboard protocol key events (`CSI u`)

    use crate::keys::{KeyCode as K, KeyEvent, Modifiers as M};

    /// Special key code points (Unicode Private Use Area)
    const INSERT: u32 = 57348;
    const DELETE: u32 = 57349;
    const LEFT: u32 = 57350;
    const RIGHT: u32 = 57351;
    const UP: u32 = 57352;
    const DOWN: u32 = 57353;
    const PAGE_UP: u32 = 57354;
    const PAGE_DOWN: u32 = 57355;
    const HOME: u32 = 57356;
    const END: u32 = 57357;

    /// Parse a `CSI u` key event.
    /// `csi` is the sequence without the leading ESC, including the `CSI`
    /// introducer `[` and the final `u` (e.g. `[13;2u`, `[57350u`).
    pub(crate) fn decode(csi: &[u8]) -> Option<KeyEvent> {
        if csi.first() != Some(&b'[') || csi.last() != Some(&b'u') {
            return None;
        }
        let body = &csi[1..csi.len() - 1];
        let params: Vec<&[u8]> = body.split(|&b| b == b';').collect();
        if params.len() > 3 {
            return None;
        }
        // field 0 is the key code; it may carry alternate-key sub-fields
        // (only when the terminal reports them), so take the primary value
        let kcode = primary_num(params[0])?;
        // field 1 is the modifiers (only when the terminal reports them), so
        // take the primary value; it may carry an event-type sub-field
        let mods = if params.len() > 1 {
            mods_from(primary_num(params[1])?)
        } else {
            M::NONE
        };
        // field 2 (optional) is the text as codepoints; we don't report it,
        // so it is ignored
        Some(key_event(kcode, mods))
    }

    /// Parse the first colon-separated sub-field of a field as a number.
    fn primary_num(field: &[u8]) -> Option<u32> {
        let primary = field.split(|&b| b == b':').next()?;
        parse_num(primary)
    }

    fn parse_num(s: &[u8]) -> Option<u32> {
        if s.is_empty() {
            return None;
        }
        let mut v = 0u32;
        for &b in s {
            if !b.is_ascii_digit() {
                return None;
            }
            v = v.checked_mul(10)?.checked_add(u32::from(b - b'0'))?;
            if v > 0x10_FFFF {
                return None;
            }
        }
        Some(v)
    }

    /// The modifier field is the modifier mask plus one: `1` means no
    /// modifiers, `1 + shift` (2) means shift, `1 + ctrl` (5) means ctrl, etc.
    /// bit 0 = shift, bit 1 = alt, bit 2 = ctrl, bits 3.. are ignored
    fn mods_from(wire: u32) -> M {
        let m = wire.saturating_sub(1);
        let mut mods = M::NONE;
        if m & 1 != 0 {
            mods |= M::SHIFT;
        }
        if m & 2 != 0 {
            mods |= M::ALT;
        }
        if m & 4 != 0 {
            mods |= M::CTRL;
        }
        mods
    }

    fn key_event(kcode: u32, mods: M) -> KeyEvent {
        let k = match kcode {
            // Ctrl+H is a backspace alias; `KeyEvent::new(0x08)` yields
            // `Backspace` with no CTRL, and the keymap binds that form
            8 => return KeyEvent(K::Backspace, M::NONE),
            // Shift+Tab is `BackTab`, matching `KeyEvent::new(0x09)`
            9 => {
                if mods.contains(M::SHIFT) {
                    let mut m = mods;
                    m.remove(M::SHIFT);
                    return KeyEvent(K::BackTab, m);
                }
                K::Tab
            }
            13 => K::Enter,
            27 => K::Esc,
            127 => K::Backspace,
            INSERT => K::Insert,
            DELETE => K::Delete,
            LEFT => K::Left,
            RIGHT => K::Right,
            UP => K::Up,
            DOWN => K::Down,
            PAGE_UP => K::PageUp,
            PAGE_DOWN => K::PageDown,
            HOME => K::Home,
            END => K::End,
            57364..=57393 => K::F((kcode - 57364 + 1) as u8),
            // control keys are encoded as their control code (0..=31) with
            // the CTRL modifier; render them as the matching uppercase
            // letter + CTRL, matching `KeyEvent::new` for raw control bytes
            // (so Ctrl-D/Z/C reach the keymap's `Char(., CTRL)` bindings)
            0..=31 => {
                let c = char::from_u32(kcode + 0x40).expect("valid control letter");
                return KeyEvent(K::Char(c), mods | M::CTRL);
            }
            // surrogates, and the rest of the Private Use Area
            // (lock keys, keypad, ...): not representable as a single key event
            _ if (0xD800..=0xDFFF).contains(&kcode)
                || (57344..=63743).contains(&kcode) =>
            {
                return KeyEvent(K::UnknownEscSeq, M::NONE);
            }
            // any other valid code point
            32..=0x10_FFFF => {
                let c = char::from_u32(kcode).expect("valid code point");
                // Ctrl+letter is reported as the *uppercase* letter + CTRL
                // (matching `KeyEvent::new` for the raw control byte, and the
                // keymap's `Char(., CTRL)` bindings); kitty sends the base
                // letter codepoint with the CTRL modifier, so uppercase it.
                if mods.contains(M::CTRL) && c.is_ascii_lowercase() {
                    K::Char(c.to_ascii_uppercase())
                } else {
                    K::Char(c)
                }
            }
            _ => return KeyEvent(K::UnknownEscSeq, M::NONE),
        };
        KeyEvent(k, mods)
    }

    #[cfg(test)]
    mod tests {
        use super::{K, KeyEvent, M, decode};

        #[test]
        fn decode_simple() {
            assert_eq!(decode(b"[13u"), Some(KeyEvent(K::Enter, M::NONE)));
            assert_eq!(decode(b"[97u"), Some(KeyEvent(K::Char('a'), M::NONE)));
            assert_eq!(decode(b"[57350u"), Some(KeyEvent(K::Left, M::NONE)));
            assert_eq!(decode(b"[57364u"), Some(KeyEvent(K::F(1), M::NONE)));
            assert_eq!(decode(b"[57376u"), Some(KeyEvent(K::F(13), M::NONE)));
            assert_eq!(decode(b"[57393u"), Some(KeyEvent(K::F(30), M::NONE)));
        }

        // modifier field: wire value is (1 + mask);
        // shift=1, alt=2, ctrl=4, super=8, hyper=16, meta=32,
        // caps_lock=64, num_lock=128
        #[test]
        fn decode_mods() {
            // a modifier field of 1 (or its absence) means no modifiers
            assert_eq!(decode(b"[13;1u"), Some(KeyEvent(K::Enter, M::NONE)));
            // shift (1 + 1 = 2)
            assert_eq!(decode(b"[13;2u"), Some(KeyEvent(K::Enter, M::SHIFT)));
            // alt (1 + 2 = 3)
            assert_eq!(decode(b"[13;3u"), Some(KeyEvent(K::Enter, M::ALT)));
            // ctrl (1 + 4 = 5)
            assert_eq!(decode(b"[13;5u"), Some(KeyEvent(K::Enter, M::CTRL)));
            // shift | ctrl (1 + 5 = 6)
            assert_eq!(
                decode(b"[13;6u"),
                Some(KeyEvent(K::Enter, M::SHIFT | M::CTRL))
            );
            // ctrl + left (1 + 4 = 5)
            assert_eq!(decode(b"[57350;5u"), Some(KeyEvent(K::Left, M::CTRL)));
            // super (1 + 8 = 9) has no corresponding modifier, is ignored
            assert_eq!(decode(b"[97;9u"), Some(KeyEvent(K::Char('a'), M::NONE)));
            // caps_lock (1 + 64 = 65) has no corresponding modifier, is ignored
            assert_eq!(decode(b"[97;65u"), Some(KeyEvent(K::Char('a'), M::NONE)));
        }

        #[test]
        fn decode_tab_and_shift_tab() {
            assert_eq!(decode(b"[9u"), Some(KeyEvent(K::Tab, M::NONE)));
            assert_eq!(
                decode(b"[9;2u"),
                Some(KeyEvent(K::BackTab, M::NONE))
            );
        }

        #[test]
        fn decode_ctrl_letter() {
            // terminals send Ctrl+letter as the *letter* codepoint + CTRL
            // modifier; it is decoded as the uppercase letter + CTRL so it
            // matches the keymap's `Char(., CTRL)` bindings
            assert_eq!(
                decode(b"[100;5u"),
                Some(KeyEvent(K::Char('D'), M::CTRL))
            );
            assert_eq!(
                decode(b"[122;5u"),
                Some(KeyEvent(K::Char('Z'), M::CTRL))
            );
            assert_eq!(
                decode(b"[99;5u"),
                Some(KeyEvent(K::Char('C'), M::CTRL))
            );
            // a non-letter is left as-is
            assert_eq!(
                decode(b"[32;5u"),
                Some(KeyEvent(K::Char(' '), M::CTRL))
            );
        }

        #[test]
        fn decode_control_code_keys() {
            // some encoders send the control code itself (0..=31); decode it
            // the same way as the letter form
            assert_eq!(
                decode(b"[4;5u"),
                Some(KeyEvent(K::Char('D'), M::CTRL))
            );
            assert_eq!(
                decode(b"[26;5u"),
                Some(KeyEvent(K::Char('Z'), M::CTRL))
            );
            assert_eq!(
                decode(b"[3;5u"),
                Some(KeyEvent(K::Char('C'), M::CTRL))
            );
            // CTRL is implied by the control code even when the modifier
            // field reports none
            assert_eq!(
                decode(b"[4;1u"),
                Some(KeyEvent(K::Char('D'), M::CTRL))
            );
            // Ctrl+H is a backspace alias (no CTRL, matching legacy)
            assert_eq!(decode(b"[8u"), Some(KeyEvent(K::Backspace, M::NONE)));
            assert_eq!(
                decode(b"[8;5u"),
                Some(KeyEvent(K::Backspace, M::NONE))
            );
            // code 0 maps to '@', as `KeyEvent::new('\x00')` does
            assert_eq!(
                decode(b"[0;5u"),
                Some(KeyEvent(K::Char('@'), M::CTRL))
            );
        }

        #[test]
        fn decode_with_text() {
            // the third parameter (text as codepoints) is ignored
            // (spec example: shift+a -> CSI 97;2;65 u)
            assert_eq!(decode(b"[97;2;65u"), Some(KeyEvent(K::Char('a'), M::SHIFT)));
            // an event-type sub-field in the modifier field is ignored
            assert_eq!(decode(b"[13;2:1u"), Some(KeyEvent(K::Enter, M::SHIFT)));
        }

        #[test]
        fn decode_unknown() {
            // lock key
            assert_eq!(
                decode(b"[57358u"),
                Some(KeyEvent(K::UnknownEscSeq, M::NONE))
            );
            // F31 and above are not representable
            assert_eq!(
                decode(b"[57394u"),
                Some(KeyEvent(K::UnknownEscSeq, M::NONE))
            );
            // out of range
            assert_eq!(decode(b"[1114112u"), None);
            // surrogate
            assert_eq!(
                decode(b"[55296u"),
                Some(KeyEvent(K::UnknownEscSeq, M::NONE))
            );
            // malformed
            assert_eq!(decode(b"[13;"), None);
            assert_eq!(decode(b"[;u"), None);
            assert_eq!(decode(b"[13;2"), None);
            assert_eq!(decode(b"[13;2uX"), None);
            assert_eq!(decode(b"[]13u"), None);
        }
    }
}

#[cfg(all(test, feature = "kitty-keyboard-protocol"))]
mod test_kitty {
    use std::io::Write as _;
    use std::os::fd::AsRawFd as _;

    use super::{AltFd, PosixRawReader, RawReader as _, UnixStream};
    use crate::config::Config;
    use crate::keys::{KeyCode as K, KeyEvent, Modifiers as M};

    /// Write `input` bytes to a kitty-mode reader and check that it produces
    /// exactly the given key events and nothing else (all input consumed).
    fn read_kitty(input: &[u8], expected: &[KeyEvent]) {
        let (mut writer, reader) = UnixStream::pair().unwrap();
        let mut rdr = PosixRawReader::new(
            AltFd(reader.as_raw_fd()),
            None,
            None,
            &Config::default(),
            Default::default(),
            None,
            true,       // kitty
            Vec::new(), // pending
            #[cfg(target_os = "macos")]
            false,
        );
        writer.write_all(input).unwrap();
        drop(writer);
        let mut n = 0;
        while let Ok(key) = rdr.next_key(false) {
            let exp = expected.get(n).expect("more keys than expected");
            assert_eq!(key, *exp, "unexpected key {n}");
            n += 1;
        }
        assert_eq!(n, expected.len(), "fewer keys than expected");
        assert!(rdr.pushback.is_empty());
    }

    #[test]
    fn kitty_shift_enter() {
        // the motivating case: kitty shift+enter is CSI 13;2 u
        // (modifier field is 1 + mask; shift = 1 + 1 = 2)
        read_kitty(b"\x1b[13;2u", &[KeyEvent(K::Enter, M::SHIFT)]);
    }

    #[test]
    fn kitty_ctrl_char() {
        // ctrl+a is CSI 97;5 u (1 + 4 = 5); decoded as the uppercase
        // letter + CTRL to match the keymap's `Char(., CTRL)` bindings
        read_kitty(b"\x1b[97;5u", &[KeyEvent(K::Char('A'), M::CTRL)]);
    }

    #[test]
    fn kitty_pua_mods() {
        // ctrl+left arrow is CSI 57350;5 u (1 + 4 = 5)
        read_kitty(b"\x1b[57350;5u", &[KeyEvent(K::Left, M::CTRL)]);
    }

    #[test]
    fn kitty_unknown_key() {
        // a key we don't represent (caps lock) becomes UnknownEscSeq
        read_kitty(b"\x1b[57358u", &[KeyEvent(K::UnknownEscSeq, M::NONE)]);
    }

    #[test]
    fn kitty_legacy_fallback() {
        // an unmodified arrow still comes as a legacy CSI (pushback path)
        read_kitty(b"\x1b[D", &[KeyEvent(K::Left, M::NONE)]);
    }

    #[test]
    fn kitty_raw_bytes() {
        // enter/tab/letters are sent as raw bytes, not CSI u
        read_kitty(
            b"a\r",
            &[KeyEvent(K::Char('a'), M::NONE), KeyEvent(K::Enter, M::NONE)],
        );
    }
}

#[cfg(test)]
mod test {
    use super::{AltFd, Position, PosixRenderer, PosixTerminal, Renderer as _};
    use crate::config::BellStyle;
    use crate::layout::GraphemeClusterMode;
    use crate::line_buffer::{LineBuffer, NoListener};

    #[test]
    #[ignore]
    fn prompt_with_ansi_escape_codes() {
        let out = PosixRenderer::new(
            AltFd(libc::STDOUT_FILENO),
            4,
            true,
            true,
            GraphemeClusterMode::default(),
            BellStyle::default(),
        );
        let pos = out.calculate_position("\x1b[1;32m>>\x1b[0m ", Position::default());
        assert_eq!(3, pos.col);
        assert_eq!(0, pos.row);
    }

    #[test]
    fn test_send() {
        fn assert_send<T: Send>() {}
        assert_send::<PosixTerminal>();
    }

    #[test]
    fn test_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<PosixTerminal>();
    }

    #[test]
    fn test_line_wrap() {
        let mut out = PosixRenderer::new(
            AltFd(libc::STDOUT_FILENO),
            4,
            true,
            true,
            GraphemeClusterMode::default(),
            BellStyle::default(),
        );
        let prompt = "> ";
        let default_prompt = true;
        let prompt_size = out.calculate_position(prompt, Position::default());

        let mut line = LineBuffer::init("", 0);
        let old_layout = out.compute_layout(prompt_size, default_prompt, &line, None);
        assert_eq!(Position { col: 2, row: 0 }, old_layout.cursor);
        assert_eq!(old_layout.cursor, old_layout.end);

        assert_eq!(
            Some(true),
            line.insert('a', out.cols - prompt_size.col + 1, &mut NoListener)
        );
        let new_layout = out.compute_layout(prompt_size, default_prompt, &line, None);
        assert_eq!(Position { col: 1, row: 1 }, new_layout.cursor);
        assert_eq!(new_layout.cursor, new_layout.end);
        out.refresh_line(prompt, &line, None, Some(&old_layout), &new_layout, None)
            .unwrap();
        #[rustfmt::skip]
        assert_eq!(
            "\r\u{1b}[K> aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\r\u{1b}[1C",
            out.buffer
        );
    }
}
