//! Translation validation for obligation F3: the naga IR that the WGSL front
//! end produces for selected kernels equals the expression trees whose error
//! bounds are proved in Lean (`verification/fixtures/kernels.sexp` and
//! `kernels-branching.sexp`, which `BlackHole.KernelFixture` proves equal to
//! the Lean definitions).
//!
//! Trees are compared after flattening and sorting sums, and sorting the
//! operands of products, `max` and `min`. The Lean bounds are unchanged by
//! these (`WgslPoly`, `WgslExpr`), and naga leaves the summation order of `dot`
//! and matrix products to the backend. Constants are compared as exact dyadic
//! rationals. Branches become `if l < r { x } else { y }` nodes using exact
//! rewrites for non-NaN values: `a <= b` is `!(b < a)`, `-a < c` is `-c < a`,
//! and `s == 0` is `!(-s < 0)` when `s` is a sum, square, `abs`, `sqrt` or
//! `max` that cannot be negative. WGSL builtins that are defined by formulas
//! (`clamp`, `length`, `normalize`, `cross`) expand to those formulas.

use naga::{
    ArraySize, BinaryOperator, Expression, Handle, Literal, MathFunction, Module, ScalarKind,
    Statement, TypeInner,
};
use std::collections::HashMap;

#[allow(dead_code)] // only compile_wesl is used here
mod common;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Tree {
    In(u32),
    /// `m * 2^e`, normalized so `m` is odd or zero (then `e = 0`).
    C(i128, i32),
    Add(Vec<Tree>),
    Mul(Vec<Tree>),
    Sub(Box<Tree>, Box<Tree>),
    Neg(Box<Tree>),
    Div(Box<Tree>, Box<Tree>),
    /// Builtins: `max`, `min`, `abs`, `sqrt`, `invsqrt`, `exp`, `log`, ...
    F(String, Vec<Tree>),
    /// `[l, r, x, y]`: `if l < r { x } else { y }`.
    Sel(Vec<Tree>),
}

const ZERO: Tree = Tree::C(0, 0);

fn f(name: &str, args: Vec<Tree>) -> Tree {
    Tree::F(name.into(), args)
}

fn dyadic(mut m: i128, mut e: i32) -> Tree {
    if m == 0 {
        return ZERO;
    }
    while m % 2 == 0 {
        m /= 2;
        e += 1;
    }
    Tree::C(m, e)
}

fn f32_value(x: f32) -> Tree {
    let bits = x.to_bits();
    let exponent = ((bits >> 23) & 0xff) as i32;
    let fraction = (bits & 0x7f_ffff) as i128;
    assert_ne!(exponent, 255, "non-finite literal");
    let (m, e) = if exponent == 0 {
        (fraction, -149)
    } else {
        (fraction | 1 << 23, exponent - 150)
    };
    dyadic(if bits >> 31 == 1 { -m } else { m }, e)
}

fn rational(num: &str, den: &str) -> Tree {
    let num: i128 = num.parse().expect("numerator");
    let den: u128 = den.parse().expect("denominator fits in u128");
    assert!(den.is_power_of_two(), "non-dyadic constant {num}/{den}");
    dyadic(num, -(den.trailing_zeros() as i32))
}

fn normalize(t: Tree) -> Tree {
    match t {
        Tree::Add(cs) => {
            let mut flat = Vec::new();
            for c in cs {
                match normalize(c) {
                    Tree::Add(inner) => flat.extend(inner),
                    c => flat.push(c),
                }
            }
            flat.sort();
            Tree::Add(flat)
        }
        Tree::Mul(cs) => {
            let mut cs: Vec<Tree> = cs.into_iter().map(normalize).collect();
            cs.sort();
            Tree::Mul(cs)
        }
        Tree::F(name, cs) => {
            let mut cs: Vec<Tree> = cs.into_iter().map(normalize).collect();
            if name == "max" || name == "min" {
                cs.sort();
            }
            Tree::F(name, cs)
        }
        Tree::Sel(cs) => {
            let mut cs: Vec<Tree> = cs.into_iter().map(normalize).collect();
            if let (Tree::Neg(a), Tree::C(m, e)) = (&cs[0], &cs[1]) {
                (cs[0], cs[1]) = (dyadic(-m, *e), (**a).clone());
            }
            Tree::Sel(cs)
        }
        Tree::Sub(a, b) => Tree::Sub(Box::new(normalize(*a)), Box::new(normalize(*b))),
        Tree::Neg(a) => Tree::Neg(Box::new(normalize(*a))),
        Tree::Div(a, b) => Tree::Div(Box::new(normalize(*a)), Box::new(normalize(*b))),
        t => t,
    }
}

fn children(t: &Tree) -> Vec<&Tree> {
    match t {
        Tree::Add(cs) | Tree::Mul(cs) | Tree::F(_, cs) | Tree::Sel(cs) => cs.iter().collect(),
        Tree::Sub(x, y) | Tree::Div(x, y) => vec![x, y],
        Tree::Neg(x) => vec![x],
        _ => vec![],
    }
}

/// Path to the first place two trees differ, for a readable failure.
fn difference(a: &Tree, b: &Tree, path: &str) -> Option<String> {
    if a == b {
        return None;
    }
    let (ca, cb) = (children(a), children(b));
    let same_head = std::mem::discriminant(a) == std::mem::discriminant(b)
        && ca.len() == cb.len()
        && !ca.is_empty()
        && match (a, b) {
            (Tree::F(x, _), Tree::F(y, _)) => x == y,
            _ => true,
        };
    if same_head {
        for (i, (x, y)) in ca.into_iter().zip(cb).enumerate() {
            if let Some(d) = difference(x, y, &format!("{path}/{i}")) {
                return Some(d);
            }
        }
    }
    let short = |t: &Tree| format!("{t:?}").chars().take(400).collect::<String>();
    Some(format!(
        "at {path}:\n  naga: {}\n  lean: {}",
        short(a),
        short(b)
    ))
}

fn parse_sexp(toks: &[&str], pos: &mut usize) -> Tree {
    let mut next = || {
        *pos += 1;
        toks[*pos - 1]
    };
    assert_eq!(next(), "(");
    let op = next();
    let t = match op {
        "in" => Tree::In(next().parse().unwrap()),
        "c" => {
            let (n, d) = (next(), next());
            rational(n, d)
        }
        "divc" => {
            let a = parse_sexp(toks, pos);
            let (n, d) = (toks[*pos], toks[*pos + 1]);
            *pos += 2;
            Tree::Div(Box::new(a), Box::new(rational(n, d)))
        }
        "lt" => {
            let a = parse_sexp(toks, pos);
            let t = rational(toks[*pos], toks[*pos + 1]);
            *pos += 2;
            let (x, y) = (parse_sexp(toks, pos), parse_sexp(toks, pos));
            Tree::Sel(vec![a, t, x, y])
        }
        _ => {
            let mut cs = Vec::new();
            while toks[*pos] == "(" {
                cs.push(parse_sexp(toks, pos));
            }
            let pair = |mut cs: Vec<Tree>| {
                let b = cs.pop().unwrap();
                (Box::new(cs.pop().unwrap()), Box::new(b))
            };
            match op {
                "add" => Tree::Add(cs),
                "mul" => Tree::Mul(cs),
                "sub" => {
                    let (a, b) = pair(cs);
                    Tree::Sub(a, b)
                }
                "div" => {
                    let (a, b) = pair(cs);
                    Tree::Div(a, b)
                }
                "neg" => Tree::Neg(Box::new(cs.pop().unwrap())),
                "lt2" => Tree::Sel(cs),
                _ => Tree::F(op.into(), cs),
            }
        }
    };
    assert_eq!(toks[*pos], ")");
    *pos += 1;
    t
}

/// Fixture entries by kernel name, in output order.
fn fixture() -> HashMap<String, Vec<Tree>> {
    let text = [
        include_str!("../verification/fixtures/kernels.sexp"),
        include_str!("../verification/fixtures/kernels-branching.sexp"),
    ]
    .concat();
    let mut entries: HashMap<String, Vec<Tree>> = HashMap::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let spaced = line.replace('(', " ( ").replace(')', " ) ");
        let tokens: Vec<&str> = spaced.split_whitespace().collect();
        let mut pos = 1;
        let tree = parse_sexp(&tokens, &mut pos);
        assert_eq!(pos, tokens.len(), "trailing tokens in {}", tokens[0]);
        entries.entry(tokens[0].to_string()).or_default().push(tree);
    }
    entries
}

fn rename(t: &Tree, f: &dyn Fn(u32) -> u32) -> Tree {
    let all = |cs: &[Tree]| cs.iter().map(|c| rename(c, f)).collect();
    let bx = |c: &Tree| Box::new(rename(c, f));
    match t {
        Tree::In(i) => Tree::In(f(*i)),
        Tree::C(..) => t.clone(),
        Tree::Add(cs) => Tree::Add(all(cs)),
        Tree::Mul(cs) => Tree::Mul(all(cs)),
        Tree::F(n, cs) => Tree::F(n.clone(), all(cs)),
        Tree::Sel(cs) => Tree::Sel(all(cs)),
        Tree::Sub(a, b) => Tree::Sub(bx(a), bx(b)),
        Tree::Div(a, b) => Tree::Div(bx(a), bx(b)),
        Tree::Neg(a) => Tree::Neg(bx(a)),
    }
}

fn compare(computed: Vec<Tree>, lean: &[Tree], name: &str) {
    assert_eq!(computed.len(), lean.len(), "{name}: output count");
    for (i, (tree, lean)) in computed.into_iter().zip(lean).enumerate() {
        let lean = normalize(lean.clone());
        if let Some(d) = difference(&normalize(tree), &lean, &format!("{name}.{i}")) {
            panic!("naga IR differs from the Lean model {d}");
        }
    }
}

/// A branch condition on computed values.
#[derive(Clone, Debug)]
enum Cond {
    Const(bool),
    Lt(Tree, Tree),
    Le(Tree, Tree),
    Eq(Tree, Tree),
    /// An untracked flag: both branches must agree on every computed value.
    Unknown,
}

/// Values that cannot be negative in any WGSL evaluation.
fn nonneg(t: &Tree) -> bool {
    match t {
        Tree::C(m, _) => *m >= 0,
        Tree::F(name, cs) => match name.as_str() {
            "abs" | "sqrt" => true,
            "max" => cs.iter().any(nonneg),
            _ => false,
        },
        Tree::Add(cs) => cs.iter().all(nonneg),
        Tree::Mul(cs) => cs.len() == 2 && cs[0] == cs[1] || cs.iter().all(nonneg),
        _ => false,
    }
}

fn select(cond: Cond, x: Tree, y: Tree) -> Tree {
    if x == y {
        return x;
    }
    match cond {
        Cond::Const(b) => {
            if b {
                x
            } else {
                y
            }
        }
        Cond::Lt(a, b) => Tree::Sel(vec![a, b, x, y]),
        Cond::Le(a, b) => Tree::Sel(vec![b, a, y, x]),
        Cond::Eq(s, z) if z == ZERO && nonneg(&s) => {
            Tree::Sel(vec![Tree::Neg(Box::new(s)), ZERO, y, x])
        }
        Cond::Eq(a, b) => panic!("no exact encoding of {a:?} == {b:?}"),
        Cond::Unknown => panic!("a branch on an untracked flag changes a computed value"),
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Scalar(Tree),
    Vector(Vec<Tree>),
    /// Columns.
    Matrix(Vec<Vec<Tree>>),
    /// Structs and arrays.
    Struct(Vec<Value>),
    Int(i64),
    Bool(BoolValue),
    /// A flag the Lean models do not track (`Metric.valid`).
    Unknown,
}

/// Conditions are never treated as equal, so merges keep both branches.
#[derive(Clone, Debug)]
struct BoolValue(Cond);

impl PartialEq for BoolValue {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl Value {
    fn scalar(self) -> Tree {
        match self {
            Value::Scalar(t) => t,
            v => panic!("expected scalar, got {v:?}"),
        }
    }
    fn int(self) -> i64 {
        match self {
            Value::Int(i) => i,
            v => panic!("expected integer, got {v:?}"),
        }
    }
    fn cond(self) -> Cond {
        match self {
            Value::Bool(BoolValue(c)) => c,
            Value::Unknown => Cond::Unknown,
            v => panic!("expected bool, got {v:?}"),
        }
    }
    /// The floating-point components; flags are dropped.
    fn flatten(self, out: &mut Vec<Tree>) {
        match self {
            Value::Scalar(t) => out.push(t),
            Value::Vector(v) => out.extend(v),
            Value::Matrix(cols) => cols.into_iter().for_each(|c| out.extend(c)),
            Value::Struct(fields) => fields.into_iter().for_each(|f| f.flatten(out)),
            Value::Bool(_) | Value::Unknown => {}
            Value::Int(i) => panic!("integer output {i}"),
        }
    }
    fn get(&self, path: &[usize]) -> Value {
        let Some((&i, rest)) = path.split_first() else {
            return self.clone();
        };
        match self {
            Value::Struct(f) => f[i].get(rest),
            Value::Matrix(m) => Value::Vector(m[i].clone()).get(rest),
            Value::Vector(v) if rest.is_empty() => Value::Scalar(v[i].clone()),
            v => panic!("path {path:?} into {v:?}"),
        }
    }
    fn set(&mut self, path: &[usize], new: Value) {
        let Some((&i, rest)) = path.split_first() else {
            *self = new;
            return;
        };
        match self {
            Value::Struct(f) => f[i].set(rest, new),
            Value::Matrix(m) => {
                let mut col = Value::Vector(m[i].clone());
                col.set(rest, new);
                let Value::Vector(c) = col else {
                    unreachable!()
                };
                m[i] = c;
            }
            Value::Vector(v) if rest.is_empty() => v[i] = new.scalar(),
            v => panic!("path {path:?} into {v:?}"),
        }
    }
}

fn select_value(cond: &Cond, a: Value, b: Value) -> Value {
    use Value::*;
    let pick = |x: Vec<Tree>, y: Vec<Tree>| -> Vec<Tree> {
        x.into_iter()
            .zip(y)
            .map(|(x, y)| select(cond.clone(), x, y))
            .collect()
    };
    match (a, b) {
        (a, b) if a == b => a,
        (Scalar(x), Scalar(y)) => Scalar(select(cond.clone(), x, y)),
        (Vector(x), Vector(y)) => Vector(pick(x, y)),
        (Matrix(x), Matrix(y)) => Matrix(x.into_iter().zip(y).map(|(x, y)| pick(x, y)).collect()),
        (Struct(x), Struct(y)) => Struct(
            x.into_iter()
                .zip(y)
                .map(|(x, y)| select_value(cond, x, y))
                .collect(),
        ),
        (Bool(_) | Unknown, Bool(_) | Unknown) => Unknown,
        (a, b) => panic!("cannot merge {a:?} and {b:?}"),
    }
}

fn zero(module: &Module, ty: Handle<naga::Type>) -> Value {
    match &module.types[ty].inner {
        TypeInner::Scalar(s) => match s.kind {
            ScalarKind::Float => Value::Scalar(ZERO),
            ScalarKind::Bool => Value::Bool(BoolValue(Cond::Const(false))),
            _ => Value::Int(0),
        },
        TypeInner::Vector { size, .. } => Value::Vector(vec![ZERO; *size as usize]),
        TypeInner::Matrix { columns, rows, .. } => {
            Value::Matrix(vec![vec![ZERO; *rows as usize]; *columns as usize])
        }
        TypeInner::Struct { members, .. } => {
            Value::Struct(members.iter().map(|m| zero(module, m.ty)).collect())
        }
        TypeInner::Array {
            base,
            size: ArraySize::Constant(n),
            ..
        } => Value::Struct(vec![zero(module, *base); n.get() as usize]),
        t => panic!("unsupported zero value {t:?}"),
    }
}

/// Applies `f` lane by lane, broadcasting scalars against vectors.
fn lanes(args: Vec<Value>, f: impl Fn(Vec<Tree>) -> Tree) -> Value {
    let width = args.iter().find_map(|a| match a {
        Value::Vector(v) => Some(v.len()),
        _ => None,
    });
    let lane = |i: usize| -> Vec<Tree> {
        args.iter()
            .map(|a| match a {
                Value::Scalar(t) => t.clone(),
                Value::Vector(v) => v[i].clone(),
                a => panic!("lane of {a:?}"),
            })
            .collect()
    };
    match width {
        None => Value::Scalar(f(lane(0))),
        Some(n) => Value::Vector((0..n).map(|i| f(lane(i))).collect()),
    }
}

fn binary(op: BinaryOperator, a: Value, b: Value) -> Value {
    use BinaryOperator as B;
    use Value::*;
    let flag = |c: Cond| Bool(BoolValue(c));
    match (op, a, b) {
        (B::Add, Int(x), Int(y)) => Int(x + y),
        (B::Subtract, Int(x), Int(y)) => Int(x - y),
        (B::Less, Int(x), Int(y)) => flag(Cond::Const(x < y)),
        (B::Equal, Int(x), Int(y)) => flag(Cond::Const(x == y)),
        (B::NotEqual, Int(x), Int(y)) => flag(Cond::Const(x != y)),
        (B::LogicalAnd | B::LogicalOr, Unknown, _) | (B::LogicalAnd | B::LogicalOr, _, Unknown) => {
            Unknown
        }
        (B::Less | B::LessEqual | B::Greater | B::GreaterEqual | B::Equal, Scalar(x), Scalar(y)) => {
            flag(match op {
                B::Less => Cond::Lt(x, y),
                B::Greater => Cond::Lt(y, x),
                B::LessEqual => Cond::Le(x, y),
                B::GreaterEqual => Cond::Le(y, x),
                _ => Cond::Eq(x, y),
            })
        }
        (B::Multiply, Matrix(m), Vector(v)) => {
            // Row r of M v sums M[c][r] v[c] over columns c.
            let rows = m[0].len();
            Vector(
                (0..rows)
                    .map(|r| {
                        Tree::Add(
                            m.iter()
                                .zip(&v)
                                .map(|(col, x)| Tree::Mul(vec![col[r].clone(), x.clone()]))
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }
        (op, a, b) => {
            let node = move |x: Tree, y: Tree| match op {
                B::Add => Tree::Add(vec![x, y]),
                B::Subtract => Tree::Sub(Box::new(x), Box::new(y)),
                B::Multiply => Tree::Mul(vec![x, y]),
                B::Divide => Tree::Div(Box::new(x), Box::new(y)),
                op => panic!("unsupported operator {op:?}"),
            };
            match (a, b) {
                (Matrix(x), Matrix(y)) if op != B::Multiply => Matrix(
                    x.into_iter()
                        .zip(y)
                        .map(|(a, b)| a.into_iter().zip(b).map(|(x, y)| node(x, y)).collect())
                        .collect(),
                ),
                (Scalar(s), Matrix(m)) => Matrix(
                    m.into_iter()
                        .map(|c| c.into_iter().map(|y| node(s.clone(), y)).collect())
                        .collect(),
                ),
                (a @ (Scalar(_) | Vector(_)), b @ (Scalar(_) | Vector(_))) => {
                    lanes(vec![a, b], |mut t| {
                        let y = t.pop().unwrap();
                        node(t.pop().unwrap(), y)
                    })
                }
                (a, b) => panic!("unsupported operands {op:?} {a:?} {b:?}"),
            }
        }
    }
}

fn dot(a: Vec<Tree>, b: Vec<Tree>) -> Tree {
    Tree::Add(
        a.into_iter()
            .zip(b)
            .map(|(x, y)| Tree::Mul(vec![x, y]))
            .collect(),
    )
}

fn math(fun: MathFunction, mut args: Vec<Value>) -> Value {
    use MathFunction as M;
    let unary = |name: &'static str, args: Vec<Value>| lanes(args, |t| f(name, t));
    let vector = |v: Value| match v {
        Value::Vector(v) => v,
        v => panic!("expected vector, got {v:?}"),
    };
    match fun {
        M::Dot => {
            let b = vector(args.pop().unwrap());
            Value::Scalar(dot(vector(args.pop().unwrap()), b))
        }
        M::Clamp => lanes(args, |mut t| {
            let hi = t.pop().unwrap();
            let lo = t.pop().unwrap();
            f("min", vec![f("max", vec![t.pop().unwrap(), lo]), hi])
        }),
        M::Max => unary("max", args),
        M::Min => unary("min", args),
        M::Abs => unary("abs", args),
        M::Sqrt => unary("sqrt", args),
        M::InverseSqrt => unary("invsqrt", args),
        M::Exp => unary("exp", args),
        M::Exp2 => unary("exp2", args),
        M::Log => unary("log", args),
        M::Log2 => unary("log2", args),
        M::Length => {
            let v = vector(args.pop().unwrap());
            Value::Scalar(f("sqrt", vec![dot(v.clone(), v)]))
        }
        M::Normalize => {
            let v = vector(args.pop().unwrap());
            let norm = f("sqrt", vec![dot(v.clone(), v.clone())]);
            Value::Vector(
                v.into_iter()
                    .map(|x| Tree::Div(Box::new(x), Box::new(norm.clone())))
                    .collect(),
            )
        }
        M::Cross => {
            let b = vector(args.pop().unwrap());
            let a = vector(args.pop().unwrap());
            let term = |i: usize, j: usize| {
                Tree::Sub(
                    Box::new(Tree::Mul(vec![a[i].clone(), b[j].clone()])),
                    Box::new(Tree::Mul(vec![a[j].clone(), b[i].clone()])),
                )
            };
            Value::Vector(vec![term(1, 2), term(2, 0), term(0, 1)])
        }
        fun => panic!("unsupported builtin {fun:?}"),
    }
}

/// Constructors, component access and arithmetic, shared by global and
/// function expressions; `None` for the cases that need a function frame.
fn common(
    module: &Module,
    e: &Expression,
    sub: &mut dyn FnMut(Handle<Expression>) -> Value,
) -> Option<Value> {
    Some(match e {
        Expression::Literal(Literal::F32(x)) => Value::Scalar(f32_value(*x)),
        Expression::Literal(Literal::U32(x)) => Value::Int((*x).into()),
        Expression::Literal(Literal::I32(x)) => Value::Int((*x).into()),
        Expression::Literal(Literal::Bool(b)) => Value::Bool(BoolValue(Cond::Const(*b))),
        Expression::Constant(c) => global(module, module.constants[*c].init),
        Expression::ZeroValue(ty) => zero(module, *ty),
        Expression::Compose { ty, components } => {
            let parts: Vec<Value> = components.iter().map(|c| sub(*c)).collect();
            match &module.types[*ty].inner {
                TypeInner::Vector { .. } => {
                    let mut v = Vec::new();
                    parts.into_iter().for_each(|p| p.flatten(&mut v));
                    Value::Vector(v)
                }
                TypeInner::Matrix { .. } => Value::Matrix(
                    parts
                        .into_iter()
                        .map(|p| match p {
                            Value::Vector(c) => c,
                            p => panic!("matrix column {p:?}"),
                        })
                        .collect(),
                ),
                TypeInner::Struct { .. } | TypeInner::Array { .. } => Value::Struct(parts),
                t => panic!("unsupported compose {t:?}"),
            }
        }
        Expression::Splat { size, value } => {
            Value::Vector(vec![sub(*value).scalar(); *size as usize])
        }
        Expression::AccessIndex { base, index } => sub(*base).get(&[*index as usize]),
        Expression::Access { base, index } => {
            let i = sub(*index).int() as usize;
            sub(*base).get(&[i])
        }
        Expression::Swizzle {
            size,
            vector,
            pattern,
        } => match sub(*vector) {
            Value::Vector(v) => Value::Vector(
                pattern[..*size as usize]
                    .iter()
                    .map(|c| v[*c as usize].clone())
                    .collect(),
            ),
            v => panic!("swizzle of {v:?}"),
        },
        Expression::Unary {
            op: naga::UnaryOperator::Negate,
            expr,
        } => lanes(vec![sub(*expr)], |mut t| Tree::Neg(Box::new(t.pop().unwrap()))),
        Expression::Binary { op, left, right } => binary(*op, sub(*left), sub(*right)),
        Expression::Math {
            fun,
            arg,
            arg1,
            arg2,
            arg3,
        } => {
            let args = [Some(*arg), *arg1, *arg2, *arg3]
                .into_iter()
                .flatten()
                .map(&mut *sub)
                .collect();
            math(*fun, args)
        }
        Expression::Select {
            condition,
            accept,
            reject,
        } => {
            let c = sub(*condition).cond();
            select_value(&c, sub(*accept), sub(*reject))
        }
        _ => return None,
    })
}

fn global(module: &Module, h: Handle<Expression>) -> Value {
    let e = &module.global_expressions[h];
    common(module, e, &mut |h| global(module, h))
        .unwrap_or_else(|| panic!("unsupported constant {e:?}"))
}

/// What a kernel is evaluated on, and the parts of it the Lean model
/// abstracts.
#[derive(Default)]
struct Env {
    args: Vec<Value>,
    globals: HashMap<String, Value>,
    /// Calls whose results the Lean model reads as inputs.
    opaque_calls: HashMap<&'static str, Value>,
    /// `let` values the Lean model reads as inputs: the computed value must
    /// equal the expected trees, and is then replaced.
    lets: HashMap<&'static str, (Vec<Tree>, Value)>,
    /// Values the model assumes positive; the other branch is outside it.
    positive: Vec<Tree>,
}

enum Flow {
    Next,
    Break,
    Continue,
}

/// Symbolic execution of one function; branches on computed values fork the
/// frame and merge the results into `Sel` nodes.
#[derive(Clone)]
struct Frame<'a> {
    module: &'a Module,
    func: &'a naga::Function,
    env: &'a Env,
    top: bool,
    args: Vec<Value>,
    emitted: HashMap<Handle<Expression>, Value>,
    locals: HashMap<Handle<naga::LocalVariable>, Value>,
}

impl<'a> Frame<'a> {
    /// The local variable and component path a pointer expression names.
    fn place(&mut self, h: Handle<Expression>) -> Option<(Handle<naga::LocalVariable>, Vec<usize>)> {
        match self.func.expressions[h] {
            Expression::LocalVariable(l) => Some((l, vec![])),
            Expression::AccessIndex { base, index } => {
                let mut p = self.place(base)?;
                p.1.push(index as usize);
                Some(p)
            }
            Expression::Access { base, index } => {
                let mut p = self.place(base)?;
                p.1.push(self.eval(index).int() as usize);
                Some(p)
            }
            _ => None,
        }
    }

    fn eval(&mut self, h: Handle<Expression>) -> Value {
        if let Some(v) = self.emitted.get(&h) {
            return v.clone();
        }
        let func: &'a naga::Function = self.func;
        match &func.expressions[h] {
            Expression::FunctionArgument(i) => self.args[*i as usize].clone(),
            Expression::GlobalVariable(g) => {
                let name = self.module.global_variables[*g].name.as_deref().unwrap();
                self.env
                    .globals
                    .get(name)
                    .unwrap_or_else(|| panic!("global {name} has no value"))
                    .clone()
            }
            // Globals evaluate to their values, so loads through them are reads.
            Expression::Load { pointer } => match self.place(*pointer) {
                Some((l, path)) => self.locals[&l].get(&path),
                None => self.eval(*pointer),
            },
            e => {
                let module = self.module;
                common(module, e, &mut |h| self.eval(h))
                    .unwrap_or_else(|| panic!("unsupported expression {e:?}"))
            }
        }
    }

    fn emit(&mut self, h: Handle<Expression>) {
        // Pointers into locals are resolved by the loads and stores that use them.
        if self.place(h).is_some() {
            return;
        }
        // A loop re-emits its body's expressions; each iteration recomputes them.
        self.emitted.remove(&h);
        let mut v = self.eval(h);
        let name = self.func.named_expressions.get(&h).map(String::as_str);
        if let Some((expected, replacement)) = name.filter(|_| self.top).and_then(|n| self.env.lets.get(n)) {
            let mut computed = Vec::new();
            v.flatten(&mut computed);
            compare(computed, expected, name.unwrap());
            v = replacement.clone();
        }
        self.emitted.insert(h, v);
    }

    fn resolve(&self, c: Cond) -> Cond {
        let positive = |t: &Tree| self.env.positive.contains(t);
        match c {
            Cond::Le(a, z) if z == ZERO && positive(&a) => Cond::Const(false),
            Cond::Lt(z, a) if z == ZERO && positive(&a) => Cond::Const(true),
            c => c,
        }
    }

    /// Statements that never fork; `None` for those `exec` handles.
    fn simple(&mut self, statement: &'a Statement) -> Option<Flow> {
        match statement {
            Statement::Emit(range) => range.clone().for_each(|h| self.emit(h)),
            Statement::Store { pointer, value } => {
                let (l, path) = self
                    .place(*pointer)
                    .unwrap_or_else(|| panic!("store through {:?}", self.func.expressions[*pointer]));
                let v = self.eval(*value);
                self.locals.get_mut(&l).unwrap().set(&path, v);
            }
            Statement::Call {
                function,
                arguments,
                result,
            } => {
                let args = arguments.iter().map(|a| self.eval(*a)).collect();
                let callee = &self.module.functions[*function];
                let name = callee.name.as_deref().unwrap_or_default();
                let v = match self.env.opaque_calls.get(name) {
                    Some(v) => v.clone(),
                    None => run(self.module, callee, args, self.env, false),
                };
                if let Some(r) = result {
                    self.emitted.insert(*r, v);
                }
            }
            Statement::Loop {
                body,
                continuing,
                break_if,
            } => loop {
                if let Flow::Break = self.straight(body) {
                    break;
                }
                self.straight(continuing);
                if let Some(c) = break_if {
                    let Cond::Const(stop) = self.eval(*c).cond() else {
                        panic!("loop exit depends on computed values");
                    };
                    if stop {
                        break;
                    }
                }
            },
            Statement::Break => return Some(Flow::Break),
            Statement::Continue => return Some(Flow::Continue),
            _ => return None,
        }
        Some(Flow::Next)
    }

    /// A loop body: every branch must be decided by integer values.
    fn straight(&mut self, block: &'a naga::Block) -> Flow {
        for statement in block.iter() {
            let flow = match statement {
                Statement::Block(b) => self.straight(b),
                Statement::If {
                    condition,
                    accept,
                    reject,
                } => match self.eval(*condition).cond() {
                    Cond::Const(b) => self.straight(if b { accept } else { reject }),
                    c => panic!("loop branch on computed value {c:?}"),
                },
                s => self
                    .simple(s)
                    .unwrap_or_else(|| panic!("unsupported statement in loop {s:?}")),
            };
            if !matches!(flow, Flow::Next) {
                return flow;
            }
        }
        Flow::Next
    }

    /// Runs the statements on `stack` (innermost block last) to a `return`.
    fn exec(&mut self, mut stack: Vec<&'a [Statement]>) -> Value {
        loop {
            let Some(top) = stack.last_mut() else {
                panic!("function ends without a value");
            };
            let Some((statement, rest)) = top.split_first() else {
                stack.pop();
                continue;
            };
            *top = rest;
            match statement {
                Statement::Block(b) => stack.push(b),
                Statement::Return { value } => return self.eval(value.expect("void return")),
                Statement::If {
                    condition,
                    accept,
                    reject,
                } => {
                    let c = self.eval(*condition).cond();
                    match self.resolve(c) {
                        Cond::Const(b) => stack.push(if b { accept } else { reject }),
                        c => {
                            let mut other = self.clone();
                            let mut other_stack = stack.clone();
                            other_stack.push(reject);
                            stack.push(accept);
                            let a = self.exec(stack);
                            let b = other.exec(other_stack);
                            return select_value(&c, a, b);
                        }
                    }
                }
                s => match self.simple(s) {
                    Some(Flow::Next) => {}
                    _ => panic!("unsupported statement {s:?}"),
                },
            }
        }
    }
}

fn run(module: &Module, func: &naga::Function, args: Vec<Value>, env: &Env, top: bool) -> Value {
    let mut frame = Frame {
        module,
        func,
        env,
        top,
        args,
        emitted: HashMap::new(),
        locals: HashMap::new(),
    };
    for (l, var) in func.local_variables.iter() {
        let v = match var.init {
            Some(e) => frame.eval(e),
            None => zero(module, var.ty),
        };
        frame.locals.insert(l, v);
    }
    frame.exec(vec![&func.body])
}

/// Marks inputs the Lean model does not read; any use shows up as a mismatch.
const UNUSED: u32 = u32::MAX;

fn opaque(module: &Module, ty: Handle<naga::Type>) -> Value {
    let u = || Tree::In(UNUSED);
    match &module.types[ty].inner {
        TypeInner::Scalar(s) if s.kind == ScalarKind::Bool => Value::Unknown,
        TypeInner::Scalar(_) => Value::Scalar(u()),
        TypeInner::Vector { size, .. } => Value::Vector(vec![u(); *size as usize]),
        TypeInner::Matrix { columns, rows, .. } => {
            Value::Matrix(vec![vec![u(); *rows as usize]; *columns as usize])
        }
        TypeInner::Struct { members, .. } => {
            Value::Struct(members.iter().map(|m| opaque(module, m.ty)).collect())
        }
        t => panic!("unsupported argument type {t:?}"),
    }
}

/// Lean's `inv i j = input (base + 4 i + j)` reads row `i`, column `j`;
/// WGSL `m[j][i]` is column `j`, row `i`.
fn matrix(base: u32) -> Value {
    Value::Matrix(
        (0..4)
            .map(|c| (0..4).map(|r| Tree::In(base + 4 * r + c)).collect())
            .collect(),
    )
}

fn vector(base: u32, n: u32) -> Value {
    Value::Vector((0..n).map(|i| Tree::In(base + i)).collect())
}

fn scalar(i: u32) -> Value {
    Value::Scalar(Tree::In(i))
}

/// A struct whose named members carry Lean input indices or fixed values.
fn record(module: &Module, ty: Handle<naga::Type>, fields: &[(&str, Value)]) -> Value {
    let TypeInner::Struct { members, .. } = &module.types[ty].inner else {
        panic!("expected a struct");
    };
    Value::Struct(
        members
            .iter()
            .map(|m| {
                let name = m.name.as_deref().unwrap_or_default();
                fields
                    .iter()
                    .find(|(n, _)| *n == name)
                    .map_or_else(|| opaque(module, m.ty), |(_, v)| v.clone())
            })
            .collect(),
    )
}

fn global_record(module: &Module, name: &str, fields: &[(&str, Value)]) -> HashMap<String, Value> {
    let (_, var) = module
        .global_variables
        .iter()
        .find(|(_, g)| g.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no global {name}"));
    HashMap::from([(name.to_string(), record(module, var.ty, fields))])
}

fn function<'m>(module: &'m Module, name: &str) -> &'m naga::Function {
    module
        .functions
        .iter()
        .map(|(_, f)| f)
        .find(|f| f.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no function {name}"))
}

/// Input layout of `BlackHole.WgslGeodesic`: `inv` 0–15, `dx` 16–31,
/// `dy` 32–47, `dz` 48–63, momentum 64–67, screen 68–71.
fn geodesic_rhs_setup(module: &Module, func: &naga::Function, _: &Fixture) -> Env {
    let ray = record(
        module,
        func.arguments[0].ty,
        &[("p", vector(64, 4)), ("screen", vector(68, 4))],
    );
    let metric = record(
        module,
        func.arguments[1].ty,
        &[
            ("inv", matrix(0)),
            ("dx", matrix(16)),
            ("dy", matrix(32)),
            ("dz", matrix(48)),
        ],
    );
    Env {
        args: vec![ray, metric],
        ..Env::default()
    }
}

fn scalar_setup(_: &Module, _: &naga::Function, _: &Fixture) -> Env {
    Env {
        args: vec![scalar(0)],
        ..Env::default()
    }
}

/// Every channel reads input 0, matching the one-channel Lean model.
fn tonemap_setup(_: &Module, _: &naga::Function, _: &Fixture) -> Env {
    Env {
        args: vec![Value::Vector(vec![Tree::In(0); 3])],
        ..Env::default()
    }
}

/// Stokes vector 0–3 with `polarization_view == 2` (the hue view).
fn polarization_setup(module: &Module, _: &naga::Function, _: &Fixture) -> Env {
    Env {
        args: vec![vector(0, 4)],
        globals: global_record(module, "cam", &[("polarization_view", Value::Int(2))]),
        ..Env::default()
    }
}

/// `WgslScreen.spatialUnit` with `v` at inputs 100–102 and `gamma` from the
/// metric `g` (entry `4 i + j`): `gamma[c][r] = g[c+1][r+1]`.
fn spatial_unit_setup(_: &Module, _: &naga::Function, _: &Fixture) -> Env {
    let gamma = Value::Matrix(
        (0..3)
            .map(|c| (0..3).map(|r| Tree::In(4 * (r + 1) + c + 1)).collect())
            .collect(),
    );
    Env {
        args: vec![vector(100, 3), gamma],
        ..Env::default()
    }
}

/// Input layout of `BlackHole.WgslAddKerr`: `x` 0–2, mass 6, incoming `g`
/// 8–23, `inv` 24–39, `dx/dy/dz` 40–87, clearance 88. The model reads the
/// scaled spin `a` as inputs 3–5 and `kerr_radius(x, a)` as input 7; the
/// computed `a` must equal `WgslAddKerr.spinScale` (spin 200–202, mass 6).
/// The model covers `mass > 0`; `mass <= 0` returns the input metric.
fn add_kerr_setup(module: &Module, func: &naga::Function, fixture: &Fixture) -> Env {
    let base = record(
        module,
        func.arguments[0].ty,
        &[
            ("g", matrix(8)),
            ("inv", matrix(24)),
            ("dx", matrix(40)),
            ("dy", matrix(56)),
            ("dz", matrix(72)),
            ("clearance", scalar(88)),
        ],
    );
    let spin_input = |i: u32| if i < 3 { 200 + i } else { 6 };
    let spin_scale = fixture["spin_scale"]
        .iter()
        .map(|t| rename(t, &spin_input))
        .collect();
    Env {
        args: vec![base, vector(0, 3), scalar(6), vector(200, 3)],
        opaque_calls: HashMap::from([("kerr_radius", scalar(7))]),
        lets: HashMap::from([("a", (spin_scale, vector(3, 3)))]),
        positive: vec![Tree::In(6)],
        ..Env::default()
    }
}

type Fixture = HashMap<String, Vec<Tree>>;
type Setup = fn(&Module, &naga::Function, &Fixture) -> Env;

#[rstest::rstest]
#[case::geodesic_rhs("geodesic_rhs", geodesic_rhs_setup as Setup)]
#[case::atan_poly("atan_poly", scalar_setup as Setup)]
#[case::tonemap("tonemap", tonemap_setup as Setup)]
#[case::heatmap_color("heatmap_color", scalar_setup as Setup)]
#[case::polarization_color("polarization_color", polarization_setup as Setup)]
#[case::spatial_unit("spatial_unit", spatial_unit_setup as Setup)]
#[case::add_kerr("add_kerr", add_kerr_setup as Setup)]
fn naga_ir_matches_lean_model(#[case] name: &str, #[case] setup: Setup) {
    let source = common::compile_wesl(include_str!("../assets/shaders/geodesic.wesl"));
    let module = naga::front::wgsl::parse_str(&source).expect("geodesic.wesl parses");
    let func = function(&module, name);
    let fixture = fixture();
    let env = setup(&module, func, &fixture);
    let mut out = Vec::new();
    run(&module, func, env.args.clone(), &env, true).flatten(&mut out);
    compare(out, &fixture[name], name);
}

#[test]
fn fixture_lists_the_checked_kernels() {
    let mut counts: Vec<(String, usize)> = fixture()
        .into_iter()
        .map(|(name, trees)| (name, trees.len()))
        .collect();
    counts.sort();
    let expected = [
        ("add_kerr", 81),
        ("atan_poly", 1),
        ("geodesic_rhs", 11),
        ("heatmap_color", 3),
        ("polarization_color", 3),
        ("spatial_unit", 3),
        ("spin_scale", 3),
        ("tonemap", 3),
    ];
    assert_eq!(
        counts,
        expected.map(|(n, c)| (n.to_string(), c)).to_vec()
    );
}

proptest::proptest! {
    #[test]
    fn literal_conversion_is_exact(bits in proptest::prelude::any::<u32>()) {
        let x = f32::from_bits(bits);
        proptest::prop_assume!(x.is_finite());
        let Tree::C(m, e) = f32_value(x) else { unreachable!() };
        proptest::prop_assert_eq!(m as f64 * 2f64.powi(e), x as f64);
    }
}
