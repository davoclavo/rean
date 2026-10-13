//! The operations this evaluator performs itself.
//!
//! Lean marks these `@[extern]` and its compiler emits a call into C. The
//! kernel accelerates most of the same list, for the same reason and with a
//! different purpose: chapter 13 found the checker counting down from a hundred
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
            _ => None,
        }
    }

    /// How many arguments the operation needs before it can run.
    fn arity(self) -> usize {
        match self {
            Prim::Zero => 0,
            Prim::Succ | Prim::Pred | Prim::StrLength | Prim::NatRepr => 1,
            Prim::Binary(_) | Prim::Compare(_) | Prim::StrAppend => 2,
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
