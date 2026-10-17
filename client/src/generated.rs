// @generated from Nanodregg.Protocol (Protocol/Table.lean) by Emit/Rust.lean. DO NOT EDIT.
// Regenerate: lake exe emit-rust client/src/generated.rs
// Check:      lake exe emit-rust --check client/src/generated.rs

pub const FRAME_BYTES_MAX: u32 = 262144;
pub const ARGV_BYTES_MAX: u32 = 65536;
pub const STEPS_PER_COMMAND_MAX: u32 = 64;
pub const SENDS_MAX: u32 = 8;
pub const CONNECTIONS_MAX: u32 = 64;

pub mod host_op {
    pub const SUBMIT: u8 = 1;
    pub const LOOKUP: u8 = 2;
    pub const READ: u8 = 3;
    pub const LOG: u8 = 4;
}

pub mod follow_op {
    pub const COMMAND: u8 = 5;
    pub const RESUME: u8 = 6;
}

pub mod status {
    pub const OK: u8 = 0;
    pub const REFUSED: u8 = 1;
    pub const UNCERTAIN: u8 = 2;
    pub const ABSENT: u8 = 3;
}

pub mod step {
    pub const DONE: u8 = 0;
    pub const SIGN: u8 = 1;
    pub const HOST: u8 = 2;
    pub const SUBMIT: u8 = 3;
}

/// The follow socket's payloads (Protocol.Table layouts; Lean codec: Protocol.Frames).
pub mod layout {

    /// Why a payload was refused: `Codec.Refusal`, with the same offsets.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Refusal {
        Truncated {
            offset: usize,
            need: usize,
        },
        Trailing {
            offset: usize,
        },
        PastBound {
            offset: usize,
            limit: usize,
            got: usize,
        },
        BadTag {
            offset: usize,
            tag: u8,
        },
    }

    struct Cursor<'a> {
        b: &'a [u8],
        i: usize,
    }

    impl Cursor<'_> {
        fn byte(&mut self) -> Result<u8, Refusal> {
            let v = *self.b.get(self.i).ok_or(Refusal::Truncated {
                offset: self.i,
                need: 1,
            })?;
            self.i += 1;
            Ok(v)
        }
        fn u32(&mut self) -> Result<usize, Refusal> {
            let four = self.b.get(self.i..self.i + 4).ok_or(Refusal::Truncated {
                offset: self.i,
                need: 4,
            })?;
            self.i += 4;
            Ok(u32::from_le_bytes([four[0], four[1], four[2], four[3]]) as usize)
        }
        fn bytes(&mut self, max: usize) -> Result<Vec<u8>, Refusal> {
            let at = self.i;
            let n = self.u32()?;
            if n > max {
                return Err(Refusal::PastBound {
                    offset: at,
                    limit: max,
                    got: n,
                });
            }
            let v = self.b.get(self.i..self.i + n).ok_or(Refusal::Truncated {
                offset: self.i,
                need: n,
            })?;
            self.i += n;
            Ok(v.to_vec())
        }
        fn list(&mut self, max: usize) -> Result<Vec<Vec<u8>>, Refusal> {
            let at = self.i;
            let n = self.u32()?;
            if n > max {
                return Err(Refusal::PastBound {
                    offset: at,
                    limit: max,
                    got: n,
                });
            }
            (0..n).map(|_| self.bytes(max)).collect()
        }
        fn end(&self) -> Result<(), Refusal> {
            if self.i == self.b.len() {
                Ok(())
            } else {
                Err(Refusal::Trailing { offset: self.i })
            }
        }
    }

    fn put_bytes(out: &mut Vec<u8>, v: &[u8], max: usize) -> Result<(), Refusal> {
        if v.len() > max {
            return Err(Refusal::PastBound {
                offset: out.len(),
                limit: max,
                got: v.len(),
            });
        }
        out.extend_from_slice(&(v.len() as u32).to_le_bytes());
        out.extend_from_slice(v);
        Ok(())
    }

    fn put_list(out: &mut Vec<u8>, v: &[Vec<u8>], max: usize) -> Result<(), Refusal> {
        if v.len() > max {
            return Err(Refusal::PastBound {
                offset: out.len(),
                limit: max,
                got: v.len(),
            });
        }
        out.extend_from_slice(&(v.len() as u32).to_le_bytes());
        v.iter().try_for_each(|x| put_bytes(out, x, max))
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Command {
        pub argv: Vec<Vec<u8>>,
    }

    impl Command {
        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {
            let mut c = Cursor { b, i: 0 };
            let argv = c.list(65536)?;
            if c.i > 65536 {
                return Err(Refusal::PastBound {
                    offset: 0,
                    limit: 65536,
                    got: c.i,
                });
            }
            c.end()?;
            Ok(Command { argv })
        }

        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {
            let mut out = Vec::new();
            let Command { argv } = self;
            put_list(&mut out, argv, 65536)?;
            if out.len() > 65536 {
                return Err(Refusal::PastBound {
                    offset: 0,
                    limit: 65536,
                    got: out.len(),
                });
            }
            Ok(out)
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Resume {
        pub k: Vec<u8>,
        pub result: Vec<u8>,
    }

    impl Resume {
        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {
            let mut c = Cursor { b, i: 0 };
            let k = c.bytes(262144)?;
            let result = c.bytes(262144)?;
            c.end()?;
            Ok(Resume { k, result })
        }

        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {
            let mut out = Vec::new();
            let Resume { k, result } = self;
            put_bytes(&mut out, k, 262144)?;
            put_bytes(&mut out, result, 262144)?;
            Ok(out)
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Step {
        Done {
            exit: u8,
            stdout: Vec<u8>,
            stderr: Vec<u8>,
        },
        Sign {
            message: Vec<u8>,
            k: Vec<u8>,
        },
        Host {
            op: u8,
            payload: Vec<u8>,
            k: Vec<u8>,
        },
        Submit {
            call: Vec<u8>,
            k: Vec<u8>,
        },
    }

    impl Step {
        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {
            let mut c = Cursor { b, i: 0 };
            let at = c.i;
            let step = match c.byte()? {
                0 => {
                    let exit = c.byte()?;
                    let stdout = c.bytes(262144)?;
                    let stderr = c.bytes(262144)?;
                    Step::Done {
                        exit,
                        stdout,
                        stderr,
                    }
                }
                1 => {
                    let message = c.bytes(262144)?;
                    let k = c.bytes(262144)?;
                    Step::Sign { message, k }
                }
                2 => {
                    let op = c.byte()?;
                    let payload = c.bytes(262144)?;
                    let k = c.bytes(262144)?;
                    Step::Host { op, payload, k }
                }
                3 => {
                    let call = c.bytes(262144)?;
                    let k = c.bytes(262144)?;
                    Step::Submit { call, k }
                }
                tag => return Err(Refusal::BadTag { offset: at, tag }),
            };
            c.end()?;
            Ok(step)
        }

        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {
            let mut out = Vec::new();
            match self {
                Step::Done {
                    exit,
                    stdout,
                    stderr,
                } => {
                    out.push(0);
                    out.push(*exit);
                    put_bytes(&mut out, stdout, 262144)?;
                    put_bytes(&mut out, stderr, 262144)?;
                }
                Step::Sign { message, k } => {
                    out.push(1);
                    put_bytes(&mut out, message, 262144)?;
                    put_bytes(&mut out, k, 262144)?;
                }
                Step::Host { op, payload, k } => {
                    out.push(2);
                    out.push(*op);
                    put_bytes(&mut out, payload, 262144)?;
                    put_bytes(&mut out, k, 262144)?;
                }
                Step::Submit { call, k } => {
                    out.push(3);
                    put_bytes(&mut out, call, 262144)?;
                    put_bytes(&mut out, k, 262144)?;
                }
            }
            Ok(out)
        }
    }
}
