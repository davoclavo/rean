//! The NDJSON reader.

use rean_core::Name;
use rean_kernel::{
    AxiomVal, BinderInfo, ConstructorVal, Declaration, DefinitionSafety, DefinitionVal,
    Environment, Expr, InductiveVal, Level, OpaqueVal, Proj, QuotKind, QuotVal, RecursorRule,
    RecursorVal, ReducibilityHints, TheoremVal,
};
use serde_json::Value;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

/// The format version that this reader was written against.
pub const KNOWN_FORMAT_VERSION: &str = "3.0.0";

/// Why a file failed to read.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExportError {
    /// A line is not valid JSON.
    BadJson { line: usize, message: String },
    /// The file does not start with a `meta` object.
    NoMeta,
    /// The format version is not one that this reader knows.
    UnknownFormat { got: String, known: String },
    /// A line refers to an index that no earlier line defined.
    MissingIndex {
        line: usize,
        kind: &'static str,
        index: i64,
    },
    /// A line has no shape that this reader knows.
    UnknownShape { line: usize, keys: String },
    /// A field is absent or has the wrong JSON type.
    BadField {
        line: usize,
        field: &'static str,
        message: String,
    },
}

impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExportError::BadJson { line, message } => {
                write!(f, "line {line}: invalid JSON: {message}")
            }
            ExportError::NoMeta => f.write_str("the file does not start with a `meta` object"),
            ExportError::UnknownFormat { got, known } => write!(
                f,
                "this reader knows export format {known}, and the file says {got}"
            ),
            ExportError::MissingIndex { line, kind, index } => {
                write!(f, "line {line}: no {kind} is defined at index {index}")
            }
            ExportError::UnknownShape { line, keys } => {
                write!(f, "line {line}: unknown shape, with keys {keys}")
            }
            ExportError::BadField {
                line,
                field,
                message,
            } => write!(f, "line {line}: field `{field}`: {message}"),
        }
    }
}

impl std::error::Error for ExportError {}

type Res<T> = Result<T, ExportError>;

/// The three version numbers from the `meta` line.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Meta {
    pub exporter_name: String,
    pub exporter_version: String,
    pub format_version: String,
    pub lean_version: String,
}

impl fmt::Display for Meta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}, format {}, Lean {}",
            self.exporter_name, self.exporter_version, self.format_version, self.lean_version
        )
    }
}

/// One file, read into an environment.
#[derive(Debug)]
pub struct Module {
    pub meta: Meta,
    pub env: Environment,
    /// Every declaration name, in the order that the file lists them.
    ///
    /// The order matters. A later declaration may use an earlier one, so a
    /// checker must walk the list front to back.
    pub order: Vec<Name>,
    /// The declarations of each line, grouped.
    ///
    /// One line of the file can declare a whole mutual group: an `inductive`
    /// line carries its types, its constructors and its recursors together.
    /// Those members refer to each other, so a checker must see all of them at
    /// once. Flattening the group would make `A.rec` unprovable until `B.rec`
    /// arrived, and the other way round.
    pub groups: Vec<Vec<Name>>,
}

/// Reads a file at `path`.
pub fn read_module(path: &str) -> Result<Module, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    Ok(read_str(&text)?)
}

/// Reads the whole text of a file.
pub fn read_str(text: &str) -> Res<Module> {
    Reader::new().run(text)
}

/// The index tables and the environment under construction.
struct Reader {
    names: HashMap<i64, Name>,
    levels: HashMap<i64, Level>,
    exprs: HashMap<i64, Expr>,
    env: Environment,
    order: Vec<Name>,
    groups: Vec<Vec<Name>>,
    /// The names of the line under read.
    current: Vec<Name>,
}

impl Reader {
    fn new() -> Self {
        let mut names = HashMap::new();
        let mut levels = HashMap::new();
        // Index 0 of each table is implicit. No line defines it.
        names.insert(0, Name::anonymous());
        levels.insert(0, Level::Zero);
        Reader {
            names,
            levels,
            exprs: HashMap::new(),
            env: Environment::new(),
            order: Vec::new(),
            groups: Vec::new(),
            current: Vec::new(),
        }
    }

    fn run(mut self, text: &str) -> Res<Module> {
        let mut meta = None;
        for (zero_based, raw) in text.lines().enumerate() {
            let line = zero_based + 1;
            if raw.trim().is_empty() {
                continue;
            }
            let value: Value = serde_json::from_str(raw).map_err(|err| ExportError::BadJson {
                line,
                message: err.to_string(),
            })?;

            if let Some(m) = value.get("meta") {
                let m = self.read_meta(line, m)?;
                if m.format_version != KNOWN_FORMAT_VERSION {
                    return Err(ExportError::UnknownFormat {
                        got: m.format_version,
                        known: KNOWN_FORMAT_VERSION.to_string(),
                    });
                }
                meta = Some(m);
                continue;
            }
            if meta.is_none() {
                return Err(ExportError::NoMeta);
            }
            self.current.clear();
            self.read_line(line, &value)?;
            if !self.current.is_empty() {
                let group = std::mem::take(&mut self.current);
                self.groups.push(group);
            }
        }

        Ok(Module {
            meta: meta.ok_or(ExportError::NoMeta)?,
            env: self.env,
            order: self.order,
            groups: self.groups,
        })
    }

    // --- one line ------------------------------------------------------

    fn read_line(&mut self, line: usize, v: &Value) -> Res<()> {
        // The index key decides which table the line fills.
        if let Some(index) = v.get("in").and_then(Value::as_i64) {
            let name = self.read_name_body(line, v)?;
            self.names.insert(index, name);
            return Ok(());
        }
        if let Some(index) = v.get("il").and_then(Value::as_i64) {
            let level = self.read_level_body(line, v)?;
            self.levels.insert(index, level);
            return Ok(());
        }
        if let Some(index) = v.get("ie").and_then(Value::as_i64) {
            let expr = self.read_expr_body(line, v)?;
            self.exprs.insert(index, expr);
            return Ok(());
        }
        self.read_declaration(line, v)
    }

    fn read_meta(&self, line: usize, v: &Value) -> Res<Meta> {
        let get = |path: [&'static str; 2]| -> Res<String> {
            v.get(path[0])
                .and_then(|o| o.get(path[1]))
                .and_then(Value::as_str)
                .map(str::to_string)
                .ok_or(ExportError::BadField {
                    line,
                    field: "meta",
                    message: format!("{}.{} is absent", path[0], path[1]),
                })
        };
        Ok(Meta {
            exporter_name: get(["exporter", "name"])?,
            exporter_version: get(["exporter", "version"])?,
            format_version: get(["format", "version"])?,
            lean_version: get(["lean", "version"])?,
        })
    }

    // --- lookups -------------------------------------------------------

    fn name(&self, line: usize, index: i64) -> Res<Name> {
        self.names
            .get(&index)
            .cloned()
            .ok_or(ExportError::MissingIndex {
                line,
                kind: "name",
                index,
            })
    }

    fn level(&self, line: usize, index: i64) -> Res<Level> {
        self.levels
            .get(&index)
            .cloned()
            .ok_or(ExportError::MissingIndex {
                line,
                kind: "level",
                index,
            })
    }

    fn expr(&self, line: usize, index: i64) -> Res<Expr> {
        self.exprs
            .get(&index)
            .cloned()
            .ok_or(ExportError::MissingIndex {
                line,
                kind: "term",
                index,
            })
    }

    /// Reads an integer field.
    fn int(&self, line: usize, v: &Value, field: &'static str) -> Res<i64> {
        v.get(field)
            .and_then(Value::as_i64)
            .ok_or(ExportError::BadField {
                line,
                field,
                message: "absent or not an integer".to_string(),
            })
    }

    /// Reads a list of integers.
    fn ints(&self, line: usize, v: &Value, field: &'static str) -> Res<Vec<i64>> {
        match v.get(field) {
            None => Ok(Vec::new()),
            Some(Value::Array(items)) => items
                .iter()
                .map(|i| {
                    i.as_i64().ok_or(ExportError::BadField {
                        line,
                        field,
                        message: "an item is not an integer".to_string(),
                    })
                })
                .collect(),
            Some(_) => Err(ExportError::BadField {
                line,
                field,
                message: "not a list".to_string(),
            }),
        }
    }

    fn name_list(&self, line: usize, v: &Value, field: &'static str) -> Res<Vec<Name>> {
        self.ints(line, v, field)?
            .into_iter()
            .map(|i| self.name(line, i))
            .collect()
    }

    fn bool_or(&self, v: &Value, field: &str, default: bool) -> bool {
        v.get(field).and_then(Value::as_bool).unwrap_or(default)
    }

    // --- names ---------------------------------------------------------

    fn read_name_body(&self, line: usize, v: &Value) -> Res<Name> {
        if let Some(part) = v.get("str") {
            let prefix = self.name(line, self.int(line, part, "pre")?)?;
            let text = part
                .get("str")
                .and_then(Value::as_str)
                .ok_or(ExportError::BadField {
                    line,
                    field: "str.str",
                    message: "absent or not a string".to_string(),
                })?;
            return Ok(prefix.str(text));
        }
        if let Some(part) = v.get("num") {
            let prefix = self.name(line, self.int(line, part, "pre")?)?;
            let number = self.int(line, part, "i")?;
            return Ok(prefix.num(number as u64));
        }
        Err(self.unknown(line, v))
    }

    // --- levels --------------------------------------------------------

    fn read_level_body(&self, line: usize, v: &Value) -> Res<Level> {
        if let Some(inner) = v.get("succ").and_then(Value::as_i64) {
            return Ok(self.level(line, inner)?.succ());
        }
        if let Some(pair) = v.get("max") {
            let [a, b] = self.pair(line, pair, "max")?;
            return Ok(self.level(line, a)?.max(&self.level(line, b)?));
        }
        if let Some(pair) = v.get("imax") {
            let [a, b] = self.pair(line, pair, "imax")?;
            return Ok(self.level(line, a)?.imax(&self.level(line, b)?));
        }
        if let Some(index) = v.get("param").and_then(Value::as_i64) {
            return Ok(Level::Param(self.name(line, index)?));
        }
        Err(self.unknown(line, v))
    }

    fn pair(&self, line: usize, v: &Value, field: &'static str) -> Res<[i64; 2]> {
        match v.as_array().map(|a| a.as_slice()) {
            Some([a, b]) => match (a.as_i64(), b.as_i64()) {
                (Some(a), Some(b)) => Ok([a, b]),
                _ => Err(ExportError::BadField {
                    line,
                    field,
                    message: "an item is not an integer".to_string(),
                }),
            },
            _ => Err(ExportError::BadField {
                line,
                field,
                message: "not a list of two".to_string(),
            }),
        }
    }

    // --- terms ---------------------------------------------------------

    fn read_expr_body(&self, line: usize, v: &Value) -> Res<Expr> {
        if let Some(index) = v.get("bvar").and_then(Value::as_i64) {
            return Ok(Expr::BVar(index as u32));
        }
        if let Some(index) = v.get("sort").and_then(Value::as_i64) {
            return Ok(Expr::Sort(self.level(line, index)?));
        }
        if let Some(body) = v.get("const") {
            let name = self.name(line, self.int(line, body, "name")?)?;
            let levels = self
                .ints(line, body, "us")?
                .into_iter()
                .map(|i| self.level(line, i))
                .collect::<Res<Vec<_>>>()?;
            return Ok(Expr::Const { name, levels });
        }
        if let Some(body) = v.get("app") {
            let fun = self.expr(line, self.int(line, body, "fn")?)?;
            let arg = self.expr(line, self.int(line, body, "arg")?)?;
            return Ok(fun.app(arg));
        }
        if let Some(body) = v.get("lam") {
            let (binder_name, binder_type, inner, info) = self.read_binder(line, body)?;
            return Ok(Expr::Lam {
                binder_name,
                binder_type: Arc::new(binder_type),
                body: Arc::new(inner),
                info,
            });
        }
        if let Some(body) = v.get("forallE") {
            let (binder_name, binder_type, inner, info) = self.read_binder(line, body)?;
            return Ok(Expr::Forall {
                binder_name,
                binder_type: Arc::new(binder_type),
                body: Arc::new(inner),
                info,
            });
        }
        if let Some(body) = v.get("letE") {
            return Ok(Expr::Let {
                binder_name: self.name(line, self.int(line, body, "name")?)?,
                binder_type: Arc::new(self.expr(line, self.int(line, body, "type")?)?),
                value: Arc::new(self.expr(line, self.int(line, body, "value")?)?),
                body: Arc::new(self.expr(line, self.int(line, body, "body")?)?),
            });
        }
        if let Some(body) = v.get("proj") {
            return Ok(Expr::Proj(Proj {
                structure: self.name(line, self.int(line, body, "typeName")?)?,
                index: self.int(line, body, "idx")? as u32,
                value: Arc::new(self.expr(line, self.int(line, body, "struct")?)?),
            }));
        }
        if let Some(digits) = v.get("natVal") {
            // The format writes the digits as a string, because a Lean `Nat`
            // has no upper bound. Our `Literal::Nat` stores them the same way.
            let digits = match digits {
                Value::String(s) => s.clone(),
                Value::Number(n) => n.to_string(),
                _ => {
                    return Err(ExportError::BadField {
                        line,
                        field: "natVal",
                        message: "not a string or a number".to_string(),
                    });
                }
            };
            return Ok(Expr::nat(digits.as_str()));
        }
        if let Some(Value::String(text)) = v.get("strVal") {
            return Ok(Expr::str(text.as_str()));
        }
        if let Some(body) = v.get("mdata") {
            // Our `Expr` has no annotation node, so the annotation goes away.
            // That is sound. `mdata` carries no meaning for the kernel.
            return self.expr(line, self.int(line, body, "expr")?);
        }
        Err(self.unknown(line, v))
    }

    fn read_binder(&self, line: usize, v: &Value) -> Res<(Name, Expr, Expr, BinderInfo)> {
        let name = self.name(line, self.int(line, v, "name")?)?;
        let ty = self.expr(line, self.int(line, v, "type")?)?;
        let body = self.expr(line, self.int(line, v, "body")?)?;
        let info = match v.get("binderInfo").and_then(Value::as_str) {
            Some("default") | None => BinderInfo::Default,
            Some("implicit") => BinderInfo::Implicit,
            Some("strictImplicit") => BinderInfo::StrictImplicit,
            Some("instImplicit") => BinderInfo::InstImplicit,
            Some(other) => {
                return Err(ExportError::BadField {
                    line,
                    field: "binderInfo",
                    message: format!("unknown value `{other}`"),
                });
            }
        };
        Ok((name, ty, body, info))
    }

    fn unknown(&self, line: usize, v: &Value) -> ExportError {
        let keys = match v {
            Value::Object(map) => map.keys().cloned().collect::<Vec<_>>().join(", "),
            other => other.to_string(),
        };
        ExportError::UnknownShape { line, keys }
    }

    // --- declarations --------------------------------------------------

    /// Reads a declaration line.
    ///
    /// The fixture wraps a `def`, `thm`, `opaque`, or `axiom` payload in an
    /// array, for a mutual group. The format document shows a single object.
    /// This reader accepts both.
    fn read_declaration(&mut self, line: usize, v: &Value) -> Res<()> {
        for (key, read) in DECL_READERS {
            if let Some(payload) = v.get(*key) {
                for one in as_group(payload) {
                    let decl = read(self, line, one)?;
                    self.order.push(decl.name().clone());
                    self.current.push(decl.name().clone());
                    self.env.add(decl);
                }
                return Ok(());
            }
        }
        if let Some(payload) = v.get("inductive") {
            return self.read_inductive(line, payload);
        }
        Err(self.unknown(line, v))
    }

    fn read_axiom(&self, line: usize, v: &Value) -> Res<Declaration> {
        Ok(Declaration::Axiom(AxiomVal {
            name: self.name(line, self.int(line, v, "name")?)?,
            level_params: self.name_list(line, v, "levelParams")?,
            ty: self.expr(line, self.int(line, v, "type")?)?,
            is_unsafe: self.bool_or(v, "isUnsafe", false),
        }))
    }

    fn read_def(&self, line: usize, v: &Value) -> Res<Declaration> {
        let hints = match v.get("hints") {
            Some(Value::String(s)) if s == "opaque" => ReducibilityHints::Opaque,
            Some(Value::String(s)) if s == "abbrev" => ReducibilityHints::Abbrev,
            Some(Value::Object(_)) => {
                ReducibilityHints::Regular(self.int(line, &v["hints"], "regular")? as u32)
            }
            _ => ReducibilityHints::Regular(0),
        };
        let safety = match v.get("safety").and_then(Value::as_str) {
            Some("unsafe") => DefinitionSafety::Unsafe,
            Some("partial") => DefinitionSafety::Partial,
            _ => DefinitionSafety::Safe,
        };
        Ok(Declaration::Definition(DefinitionVal {
            name: self.name(line, self.int(line, v, "name")?)?,
            level_params: self.name_list(line, v, "levelParams")?,
            ty: self.expr(line, self.int(line, v, "type")?)?,
            value: self.expr(line, self.int(line, v, "value")?)?,
            hints,
            safety,
            all: self.name_list(line, v, "all")?,
        }))
    }

    fn read_thm(&self, line: usize, v: &Value) -> Res<Declaration> {
        Ok(Declaration::Theorem(TheoremVal {
            name: self.name(line, self.int(line, v, "name")?)?,
            level_params: self.name_list(line, v, "levelParams")?,
            ty: self.expr(line, self.int(line, v, "type")?)?,
            value: self.expr(line, self.int(line, v, "value")?)?,
            all: self.name_list(line, v, "all")?,
        }))
    }

    fn read_opaque(&self, line: usize, v: &Value) -> Res<Declaration> {
        Ok(Declaration::Opaque(OpaqueVal {
            name: self.name(line, self.int(line, v, "name")?)?,
            level_params: self.name_list(line, v, "levelParams")?,
            ty: self.expr(line, self.int(line, v, "type")?)?,
            value: self.expr(line, self.int(line, v, "value")?)?,
            is_unsafe: self.bool_or(v, "isUnsafe", false),
            all: self.name_list(line, v, "all")?,
        }))
    }

    fn read_quot(&self, line: usize, v: &Value) -> Res<Declaration> {
        let kind = match v.get("kind").and_then(Value::as_str) {
            Some("type") => QuotKind::Type,
            Some("ctor") => QuotKind::Ctor,
            Some("lift") => QuotKind::Lift,
            Some("ind") => QuotKind::Ind,
            other => {
                return Err(ExportError::BadField {
                    line,
                    field: "quot.kind",
                    message: format!("unknown value {other:?}"),
                });
            }
        };
        Ok(Declaration::Quot(QuotVal {
            name: self.name(line, self.int(line, v, "name")?)?,
            level_params: self.name_list(line, v, "levelParams")?,
            ty: self.expr(line, self.int(line, v, "type")?)?,
            kind,
        }))
    }

    /// Reads an `inductive` line, which carries three lists.
    ///
    /// The fixture spells them `inductiveVals`, `constructorVals`, and
    /// `recursorVals`. The format document on master spells them `types`,
    /// `ctors`, and `recs`. This reader takes either.
    fn read_inductive(&mut self, line: usize, v: &Value) -> Res<()> {
        let list = |a: &'static str, b: &'static str| -> Vec<Value> {
            v.get(a)
                .or_else(|| v.get(b))
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default()
        };

        for ind in list("inductiveVals", "types") {
            let decl = Declaration::Inductive(InductiveVal {
                name: self.name(line, self.int(line, &ind, "name")?)?,
                level_params: self.name_list(line, &ind, "levelParams")?,
                ty: self.expr(line, self.int(line, &ind, "type")?)?,
                num_params: self.int(line, &ind, "numParams")? as u32,
                num_indices: self.int(line, &ind, "numIndices")? as u32,
                all: self.name_list(line, &ind, "all")?,
                ctors: self.name_list(line, &ind, "ctors")?,
                num_nested: self.int(line, &ind, "numNested").unwrap_or(0) as u32,
                is_rec: self.bool_or(&ind, "isRec", false),
                is_unsafe: self.bool_or(&ind, "isUnsafe", false),
                is_reflexive: self.bool_or(&ind, "isReflexive", false),
            });
            self.order.push(decl.name().clone());
            self.current.push(decl.name().clone());
            self.env.add(decl);
        }

        for ctor in list("constructorVals", "ctors") {
            let decl = Declaration::Constructor(ConstructorVal {
                name: self.name(line, self.int(line, &ctor, "name")?)?,
                level_params: self.name_list(line, &ctor, "levelParams")?,
                ty: self.expr(line, self.int(line, &ctor, "type")?)?,
                induct: self.name(line, self.int(line, &ctor, "induct")?)?,
                cidx: self.int(line, &ctor, "cidx")? as u32,
                num_params: self.int(line, &ctor, "numParams")? as u32,
                num_fields: self.int(line, &ctor, "numFields")? as u32,
                is_unsafe: self.bool_or(&ctor, "isUnsafe", false),
            });
            self.order.push(decl.name().clone());
            self.current.push(decl.name().clone());
            self.env.add(decl);
        }

        for rec in list("recursorVals", "recs") {
            let mut rules = Vec::new();
            for rule in rec
                .get("rules")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default()
            {
                rules.push(RecursorRule {
                    ctor: self.name(line, self.int(line, &rule, "ctor")?)?,
                    num_fields: self.int(line, &rule, "nfields")? as u32,
                    rhs: self.expr(line, self.int(line, &rule, "rhs")?)?,
                });
            }
            let decl = Declaration::Recursor(RecursorVal {
                name: self.name(line, self.int(line, &rec, "name")?)?,
                level_params: self.name_list(line, &rec, "levelParams")?,
                ty: self.expr(line, self.int(line, &rec, "type")?)?,
                all: self.name_list(line, &rec, "all")?,
                num_params: self.int(line, &rec, "numParams")? as u32,
                num_indices: self.int(line, &rec, "numIndices")? as u32,
                num_motives: self.int(line, &rec, "numMotives")? as u32,
                num_minors: self.int(line, &rec, "numMinors")? as u32,
                rules,
                k: self.bool_or(&rec, "k", false),
                is_unsafe: self.bool_or(&rec, "isUnsafe", false),
            });
            self.order.push(decl.name().clone());
            self.current.push(decl.name().clone());
            self.env.add(decl);
        }
        Ok(())
    }
}

/// A payload is either one object or a list of them, for a mutual group.
fn as_group(v: &Value) -> Vec<&Value> {
    match v {
        Value::Array(items) => items.iter().collect(),
        other => vec![other],
    }
}

type DeclReader = fn(&Reader, usize, &Value) -> Res<Declaration>;

const DECL_READERS: &[(&str, DeclReader)] = &[
    ("axiom", Reader::read_axiom),
    ("def", Reader::read_def),
    ("thm", Reader::read_thm),
    ("opaque", Reader::read_opaque),
    ("quot", Reader::read_quot),
];
