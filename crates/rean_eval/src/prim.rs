//! The operations this evaluator performs itself.
//!
//! Lean marks these `@[extern]` and its compiler emits a call into C. The
//! kernel accelerates most of the same list, for the same reason and with a
//! different purpose: chapter 21 found the checker counting down from a hundred
//! million one `Nat.succ` at a time to answer one comparison.
//!
//! Here it is not an optimisation, it is the **definition** of what running
//! means. `Nat.add` on two numbers is one instruction, and nothing in this
//! evaluator ever builds a tower.

use crate::{EvalError, EvalResult, Evaluator, Thunk, Value};
use rean_core::Name;

/// An operation that the evaluator performs itself.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    /// `Nat.zero`, which is the number and not a constructor application.
    Zero,
    /// `Nat.succ`, which adds one to a number.
    Succ,
    /// A function of two numbers that gives a number.
    Binary(Binop),
    /// A function of two numbers that gives a `Bool`.
    Compare(Compare),
    /// `Nat.pred`.
    Pred,
    /// `String.length`, in characters.
    StrLength,
    /// `String.append`.
    StrAppend,
    /// `Nat.repr` and `toString`-like, which the printer needs.
    NatRepr,
    /// `String.push`, which a `toString` chain uses to add a newline.
    StrPush,
    /// `IO.print` and `IO.println`: the effect, performed by our runtime.
    ///
    /// Lean's `IO.println` reaches `IO.getStdout`, which is `@[extern]` and is
    /// a C function, and then writes through an `IO.FS.Stream` whose fields are
    /// more C functions. A runtime has to provide that somewhere, and this is
    /// where ours does.
    ///
    /// It is higher up the chain than Lean cuts, and that is the honest limit
    /// of this evaluator: a program that writes to a stream it built itself
    /// will not run. One that says `IO.println` will.
    IoPrint { newline: bool },
}

/// A function of two numbers that gives a number.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Gcd,
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
}

/// A function of two numbers that gives a `Bool`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Compare {
    Eq,
    Le,
    Lt,
}

impl Prim {
    /// Returns the operation that `name` stands for, if this evaluator has one.
    ///
    /// The list is deliberately short. Everything absent from it **still
    /// runs**, through the definition that Lean exported, and the only cost is
    /// speed. That is the property to keep while the list grows: a primitive is
    /// a promise that our answer matches Lean's, so each one is a thing to be
    /// right about.
    pub fn of(name: &Name) -> Option<Prim> {
        match name.two_parts()? {
            ("Nat", "zero") => Some(Prim::Zero),
            ("Nat", "succ") => Some(Prim::Succ),
            ("Nat", "pred") => Some(Prim::Pred),
            ("Nat", "repr") => Some(Prim::NatRepr),
            ("Nat", "add") => Some(Prim::Binary(Binop::Add)),
            ("Nat", "sub") => Some(Prim::Binary(Binop::Sub)),
            ("Nat", "mul") => Some(Prim::Binary(Binop::Mul)),
            ("Nat", "div") => Some(Prim::Binary(Binop::Div)),
            ("Nat", "mod") => Some(Prim::Binary(Binop::Mod)),
            ("Nat", "pow") => Some(Prim::Binary(Binop::Pow)),
            ("Nat", "gcd") => Some(Prim::Binary(Binop::Gcd)),
            ("Nat", "land") => Some(Prim::Binary(Binop::And)),
            ("Nat", "lor") => Some(Prim::Binary(Binop::Or)),
            ("Nat", "xor") => Some(Prim::Binary(Binop::Xor)),
            ("Nat", "shiftLeft") => Some(Prim::Binary(Binop::ShiftLeft)),
            ("Nat", "shiftRight") => Some(Prim::Binary(Binop::ShiftRight)),
            ("Nat", "beq") => Some(Prim::Compare(Compare::Eq)),
            ("Nat", "ble") => Some(Prim::Compare(Compare::Le)),
            ("Nat", "blt") => Some(Prim::Compare(Compare::Lt)),
            ("String", "length") => Some(Prim::StrLength),
            ("String", "append") => Some(Prim::StrAppend),
            ("String", "push") => Some(Prim::StrPush),
            ("IO", "print") => Some(Prim::IoPrint { newline: false }),
            ("IO", "println") => Some(Prim::IoPrint { newline: true }),
            _ => None,
        }
    }

    /// How many arguments the operation needs before it can run.
    fn arity(self) -> usize {
        match self {
            Prim::Zero => 0,
            Prim::Succ | Prim::Pred | Prim::StrLength | Prim::NatRepr => 1,
            Prim::Binary(_) | Prim::Compare(_) | Prim::StrAppend | Prim::StrPush => 2,
            // The type, the `ToString` instance, the value, and the world.
            // The world is what makes an `IO` action a function, and giving it
            // one is what performs the effect.
            Prim::IoPrint { .. } => 4,
        }
    }
}

impl Evaluator<'_> {
    /// Runs a primitive, or waits for more arguments.
    pub(crate) fn primitive(
        &mut self,
        prim: Prim,
        name: &Name,
        args: Vec<Thunk>,
    ) -> EvalResult<Value> {
        let wanted = prim.arity();
        if args.len() < wanted {
            // Not enough yet. It stays a function, and the next application
            // will ask again with more.
            return Ok(Value::Opaque {
                head: name.clone(),
                args,
            });
        }
        let rest = args[wanted..].to_vec();
        let value = self.run_primitive(prim, name, &args[..wanted])?;
        self.apply(value, rest)
    }

    fn run_primitive(&mut self, prim: Prim, name: &Name, args: &[Thunk]) -> EvalResult<Value> {
        let number = |value: &Value| value.as_nat();
        match prim {
            Prim::Zero => Ok(Value::Nat(0)),
            Prim::Succ => {
                let inner = self.force(&args[0])?;
                match number(&inner) {
                    Some(n) => match n.checked_add(1) {
                        Some(next) => Ok(Value::Nat(next)),
                        None => Err(EvalError::PastU128("Nat.succ")),
                    },
                    // `Nat.succ` of something that is not a number is a
                    // constructor application again, which is what a recursor
                    // will take apart.
                    None => Ok(Value::Ctor {
                        name: name.clone(),
                        args: args.to_vec(),
                    }),
                }
            }
            Prim::Pred => {
                let inner = self.force(&args[0])?;
                match number(&inner) {
                    Some(n) => Ok(Value::Nat(n.saturating_sub(1))),
                    None => Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    }),
                }
            }
            Prim::NatRepr => {
                let inner = self.force(&args[0])?;
                match number(&inner) {
                    Some(n) => Ok(Value::Str(std::rc::Rc::from(n.to_string().as_str()))),
                    None => Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    }),
                }
            }
            Prim::Binary(op) => {
                let (a, b) = (self.force(&args[0])?, self.force(&args[1])?);
                let (Some(a), Some(b)) = (number(&a), number(&b)) else {
                    return Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    });
                };
                let out = match op {
                    Binop::Add => a.checked_add(b),
                    Binop::Sub => Some(a.saturating_sub(b)),
                    Binop::Mul => a.checked_mul(b),
                    // Lean defines division and modulo by zero to give zero.
                    Binop::Div => Some(a.checked_div(b).unwrap_or(0)),
                    Binop::Mod => Some(a.checked_rem(b).unwrap_or(a)),
                    Binop::Pow => u32::try_from(b).ok().and_then(|b| a.checked_pow(b)),
                    Binop::Gcd => Some(gcd(a, b)),
                    Binop::And => Some(a & b),
                    Binop::Or => Some(a | b),
                    Binop::Xor => Some(a ^ b),
                    Binop::ShiftLeft => u32::try_from(b).ok().and_then(|b| a.checked_shl(b)),
                    Binop::ShiftRight => u32::try_from(b).ok().and_then(|b| a.checked_shr(b)),
                };
                match out {
                    Some(n) => Ok(Value::Nat(n)),
                    None => Err(EvalError::PastU128(op.what())),
                }
            }
            Prim::Compare(op) => {
                let (a, b) = (self.force(&args[0])?, self.force(&args[1])?);
                let (Some(a), Some(b)) = (number(&a), number(&b)) else {
                    return Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    });
                };
                let yes = match op {
                    Compare::Eq => a == b,
                    Compare::Le => a <= b,
                    Compare::Lt => a < b,
                };
                Ok(self.boolean(yes))
            }
            Prim::StrLength => {
                let text = self.force(&args[0])?;
                match text {
                    Value::Str(text) => Ok(Value::Nat(text.chars().count() as u128)),
                    _ => Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    }),
                }
            }
            Prim::StrPush => {
                let (text, ch) = (self.force(&args[0])?, self.force(&args[1])?);
                let (Some(text), Some(code)) = (self.text_of(&text)?, self.code_point(&ch)?) else {
                    return Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    });
                };
                let Some(ch) = char::from_u32(code) else {
                    return Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    });
                };
                Ok(Value::Str(std::rc::Rc::from(
                    format!("{text}{ch}").as_str(),
                )))
            }
            Prim::IoPrint { newline } => {
                // The text is `ToString.toString α inst s`, which runs through
                // Lean's own instance. Only the write is ours.
                let shown =
                    self.constant(&Name::from_dotted("ToString.toString"), args[..3].to_vec())?;
                let Some(text) = self.text_of(&shown)? else {
                    return Err(EvalError::NotAStructure(
                        "something that is not a string, given to `IO.println`".to_string(),
                    ));
                };
                self.write(&text, newline);
                self.io_ok(args[3].clone())
            }
            Prim::StrAppend => {
                let (a, b) = (self.force(&args[0])?, self.force(&args[1])?);
                match (a, b) {
                    (Value::Str(a), Value::Str(b)) => {
                        Ok(Value::Str(std::rc::Rc::from(format!("{a}{b}").as_str())))
                    }
                    _ => Ok(Value::Opaque {
                        head: name.clone(),
                        args: args.to_vec(),
                    }),
                }
            }
        }
    }

    /// Returns `Bool.true` or `Bool.false`.
    pub(crate) fn boolean(&self, yes: bool) -> Value {
        Value::Ctor {
            name: Name::from_dotted(if yes { "Bool.true" } else { "Bool.false" }),
            args: Vec::new(),
        }
    }
}

impl Binop {
    /// The name to put in a message about a limit.
    fn what(self) -> &'static str {
        match self {
            Binop::Add => "Nat.add",
            Binop::Sub => "Nat.sub",
            Binop::Mul => "Nat.mul",
            Binop::Div => "Nat.div",
            Binop::Mod => "Nat.mod",
            Binop::Pow => "Nat.pow",
            Binop::Gcd => "Nat.gcd",
            Binop::And => "Nat.land",
            Binop::Or => "Nat.lor",
            Binop::Xor => "Nat.xor",
            Binop::ShiftLeft => "Nat.shiftLeft",
            Binop::ShiftRight => "Nat.shiftRight",
        }
    }
}

/// The greatest common divisor, by Euclid.
fn gcd(a: u128, b: u128) -> u128 {
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let next = a % b;
        a = b;
        b = next;
    }
    a
}
