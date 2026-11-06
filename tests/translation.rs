//! Translation validation for obligation F3: the naga IR that the WGSL front
//! end produces for selected kernels equals the expression trees whose error
//! bounds are proved in Lean (`verification/fixtures/kernels.sexp` and
//! `kernels-branching.sexp`, which `BlackHole.KernelFixture` proves equal to
//! the Lean definitions).
//!
//! Expressions are hash-consed into one store whose constructors normalize:
//! sums are flattened and sorted, and the operands of products, `max` and `min`
//! sorted. The Lean bounds are unchanged by these (`WgslPoly`, `WgslExpr`), and
//! naga leaves the summation order of `dot` and matrix products to the backend.
//! Two expressions agree exactly when they get the same node, so shared
//! subexpressions are compared once; sharing is only a representation, and
//! both sides denote trees. Constants are exact dyadic rationals. Branches
//! become `if l < r { x } else { y }` nodes using exact rewrites for non-NaN
//! values: `a <= b` is `!(b < a)`, `-a < c` is `-c < a`, and `s == 0` is
//! `!(-s < 0)` when `s` is a sum, square, `abs`, `sqrt` or `max` that cannot be
//! negative. WGSL builtins defined by formulas (`clamp`, `length`,
//! `normalize`, `cross`, `mix`, `smoothstep`, and the inherited `pow` and
//! `tanh`) expand to those formulas. Calls to the arithmetic `sincos` become
//! the primitives `sinS`/`cosS`, whose body `WgslSinCos` models separately.

use naga::{
    ArraySize, BinaryOperator, Expression, Handle, Literal, MathFunction, Module, ScalarKind,
    Statement, TypeInner,
};
use proptest::strategy::{Just, Strategy};
use std::collections::HashMap;

#[allow(dead_code)] // only compile_wesl is used here
mod common;

type Id = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    In(u32),
    /// `m * 2^e`, normalized so `m` is odd or zero (then `e = 0`).
    C(i128, i32),
    Add(Vec<Id>),
    Mul(Vec<Id>),
    Sub(Id, Id),
    Neg(Id),
    Div(Id, Id),
    /// Builtins: `max`, `min`, `abs`, `sqrt`, `invsqrt`, `exp`, `log`, ...
    F(String, Vec<Id>),
    /// `[l, r, x, y]`: `if l < r { x } else { y }`.
    Sel([Id; 4]),
}

/// Hash-consed expressions with normalizing constructors.
#[derive(Default)]
struct Store {
    nodes: Vec<Node>,
    index: HashMap<Node, Id>,
}

impl Store {
    fn intern(&mut self, n: Node) -> Id {
        if let Some(&id) = self.index.get(&n) {
            return id;
        }
        let id = self.nodes.len() as Id;
        self.nodes.push(n.clone());
        self.index.insert(n, id);
        id
    }
    fn input(&mut self, i: u32) -> Id {
        self.intern(Node::In(i))
    }
    fn dyadic(&mut self, mut m: i128, mut e: i32) -> Id {
        if m == 0 {
            e = 0;
        } else {
            while m % 2 == 0 {
                m /= 2;
                e += 1;
            }
        }
        self.intern(Node::C(m, e))
    }
    fn zero(&mut self) -> Id {
        self.dyadic(0, 0)
    }
    fn f32(&mut self, x: f32) -> Id {
        let (m, e) = f32_parts(x);
        self.dyadic(m, e)
    }
    fn add(&mut self, a: Id, b: Id) -> Id {
        let mut cs = Vec::new();
        for x in [a, b] {
            match &self.nodes[x as usize] {
                Node::Add(inner) => cs.extend(inner),
                _ => cs.push(x),
            }
        }
        cs.sort_unstable();
        self.intern(Node::Add(cs))
    }
    fn sum(&mut self, terms: Vec<Id>) -> Id {
        terms
            .into_iter()
            .reduce(|a, b| self.add(a, b))
            .expect("nonempty sum")
    }
    fn mul(&mut self, a: Id, b: Id) -> Id {
        self.intern(Node::Mul(vec![a.min(b), a.max(b)]))
    }
    fn sub(&mut self, a: Id, b: Id) -> Id {
        self.intern(Node::Sub(a, b))
    }
    fn div(&mut self, a: Id, b: Id) -> Id {
        self.intern(Node::Div(a, b))
    }
    fn neg(&mut self, a: Id) -> Id {
        self.intern(Node::Neg(a))
    }
    fn f(&mut self, name: &str, mut args: Vec<Id>) -> Id {
        if name == "max" || name == "min" {
            args.sort_unstable();
        }
        self.intern(Node::F(name.into(), args))
    }
    fn sel(&mut self, l: Id, r: Id, x: Id, y: Id) -> Id {
        if x == y {
            return x;
        }
        let (l, r) = match (&self.nodes[l as usize], &self.nodes[r as usize]) {
            (&Node::Neg(a), &Node::C(m, e)) => (self.dyadic(-m, e), a),
            _ => (l, r),
        };
        self.intern(Node::Sel([l, r, x, y]))
    }
    /// Values that cannot be negative in any WGSL evaluation.
    fn nonneg(&self, t: Id) -> bool {
        match &self.nodes[t as usize] {
            Node::C(m, _) => *m >= 0,
            Node::F(name, cs) => match name.as_str() {
                "abs" | "sqrt" => true,
                "max" => cs.iter().any(|&c| self.nonneg(c)),
                _ => false,
            },
            Node::Add(cs) => cs.iter().all(|&c| self.nonneg(c)),
            Node::Mul(cs) => cs[0] == cs[1] || cs.iter().all(|&c| self.nonneg(c)),
            _ => false,
        }
    }
    fn show(&self, t: Id, depth: usize) -> String {
        let n = &self.nodes[t as usize];
        let kids: Vec<Id> = match n {
            Node::In(i) => return format!("in{i}"),
            Node::C(m, e) => return format!("{m}*2^{e}"),
            Node::Add(cs) | Node::Mul(cs) | Node::F(_, cs) => cs.clone(),
            Node::Sel(cs) => cs.to_vec(),
            Node::Sub(a, b) | Node::Div(a, b) => vec![*a, *b],
            Node::Neg(a) => vec![*a],
        };
        let head = match n {
            Node::Add(_) => "add".into(),
            Node::Mul(_) => "mul".into(),
            Node::Sub(..) => "sub".into(),
            Node::Div(..) => "div".into(),
            Node::Neg(_) => "neg".into(),
            Node::Sel(_) => "sel".into(),
            Node::F(name, _) => name.clone(),
            _ => unreachable!(),
        };
        if depth == 0 {
            return format!("({head} …)");
        }
        let inner: Vec<String> = kids.iter().map(|&k| self.show(k, depth - 1)).collect();
        format!("({head} {})", inner.join(" "))
    }
}

fn f32_parts(x: f32) -> (i128, i32) {
    let bits = x.to_bits();
    let exponent = ((bits >> 23) & 0xff) as i32;
    let fraction = (bits & 0x7f_ffff) as i128;
    assert_ne!(exponent, 255, "non-finite literal");
    let (m, e) = if exponent == 0 {
        (fraction, -149)
    } else {
        (fraction | 1 << 23, exponent - 150)
    };
    (if bits >> 31 == 1 { -m } else { m }, e)
}

/// Inputs from here on name the `let` slots of a Lean model (`WgslLets`).
const LET_BASE: u32 = 1_000_000;

type Fixture = HashMap<String, Vec<Vec<String>>>;

/// Fixture rows by name, in order, as tokens.
fn fixture() -> Fixture {
    let text = [
        include_str!("../verification/fixtures/kernels.sexp"),
        include_str!("../verification/fixtures/kernels-branching.sexp"),
    ]
    .concat();
    let mut rows: Fixture = HashMap::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let spaced = line.replace('(', " ( ").replace(')', " ) ");
        let mut tokens = spaced.split_whitespace().map(String::from);
        let name = tokens.next().unwrap();
        rows.entry(name).or_default().push(tokens.collect());
    }
    rows
}

struct Parser<'a> {
    toks: &'a [String],
    pos: usize,
    lets: &'a [Id],
    rename: &'a dyn Fn(u32) -> u32,
}

impl Parser<'_> {
    fn next(&mut self) -> &str {
        self.pos += 1;
        &self.toks[self.pos - 1]
    }
    fn rational(&mut self, s: &mut Store) -> Id {
        let num: i128 = self.next().parse().expect("numerator");
        let den: u128 = self.next().parse().expect("denominator fits in u128");
        assert!(den.is_power_of_two(), "non-dyadic constant {num}/{den}");
        s.dyadic(num, -(den.trailing_zeros() as i32))
    }
    fn expr(&mut self, s: &mut Store) -> Id {
        assert_eq!(self.next(), "(");
        let op = self.next().to_string();
        let t = match op.as_str() {
            "in" => {
                let i: u32 = self.next().parse().unwrap();
                if i >= LET_BASE {
                    self.lets[(i - LET_BASE) as usize]
                } else {
                    s.input((self.rename)(i))
                }
            }
            "c" => self.rational(s),
            "divc" => {
                let a = self.expr(s);
                let c = self.rational(s);
                s.div(a, c)
            }
            "scale" => {
                let k: i32 = self.next().parse().unwrap();
                let a = self.expr(s);
                let c = s.dyadic(1, k);
                s.mul(c, a)
            }
            "lt" => {
                let a = self.expr(s);
                let t = self.rational(s);
                let (x, y) = (self.expr(s), self.expr(s));
                s.sel(a, t, x, y)
            }
            _ => {
                let mut cs = Vec::new();
                while self.toks[self.pos] == "(" {
                    cs.push(self.expr(s));
                }
                match (op.as_str(), cs.as_slice()) {
                    ("add", &[a, b]) => s.add(a, b),
                    ("mul", &[a, b]) => s.mul(a, b),
                    ("sub", &[a, b]) => s.sub(a, b),
                    ("div", &[a, b]) => s.div(a, b),
                    ("neg", &[a]) => s.neg(a),
                    ("lt2", &[a, b, x, y]) => s.sel(a, b, x, y),
                    _ => s.f(&op, cs),
                }
            }
        };
        assert_eq!(self.next(), ")");
        t
    }
}

/// The Lean model's outputs for `name`, after expanding its `let` slots.
fn lean(s: &mut Store, fixture: &Fixture, name: &str, rename: &dyn Fn(u32) -> u32) -> Vec<Id> {
    let parse = |s: &mut Store, toks: &[String], lets: &[Id]| {
        let mut p = Parser {
            toks,
            pos: 0,
            lets,
            rename,
        };
        let t = p.expr(s);
        assert_eq!(p.pos, toks.len(), "trailing tokens in {name}");
        t
    };
    let mut lets = Vec::new();
    for toks in fixture.get(&format!("{name}:let")).into_iter().flatten() {
        let t = parse(s, toks, &lets);
        lets.push(t);
    }
    fixture[name]
        .iter()
        .map(|toks| parse(s, toks, &lets))
        .collect()
}

fn compare(s: &Store, computed: &[Id], lean: &[Id], name: &str) {
    assert_eq!(computed.len(), lean.len(), "{name}: output count");
    for (i, (&a, &b)) in computed.iter().zip(lean).enumerate() {
        if a != b {
            let (x, y) = first_difference(s, a, b);
            panic!(
                "naga IR differs from the Lean model at {name}.{i}:\n  naga: {}\n  lean: {}",
                s.show(x, 5),
                s.show(y, 5)
            );
        }
    }
}

/// The innermost pair of differing nodes along matching structure.
fn first_difference(s: &Store, a: Id, b: Id) -> (Id, Id) {
    let kids = |t: Id| -> Option<(std::mem::Discriminant<Node>, String, Vec<Id>)> {
        let n = &s.nodes[t as usize];
        let (name, cs) = match n {
            Node::Add(cs) | Node::Mul(cs) => (String::new(), cs.clone()),
            Node::F(f, cs) => (f.clone(), cs.clone()),
            Node::Sel(cs) => (String::new(), cs.to_vec()),
            Node::Sub(x, y) | Node::Div(x, y) => (String::new(), vec![*x, *y]),
            Node::Neg(x) => (String::new(), vec![*x]),
            _ => return None,
        };
        Some((std::mem::discriminant(n), name, cs))
    };
    match (kids(a), kids(b)) {
        (Some((ka, na, ca)), Some((kb, nb, cb)))
            if ka == kb && na == nb && ca.len() == cb.len() =>
        {
            let sorted = matches!(s.nodes[a as usize], Node::Add(_) | Node::Mul(_))
                || na == "max"
                || na == "min";
            let pair = if sorted {
                // Operands are sorted by node, so pair what the two sides do not share.
                let only_a: Vec<Id> = ca.iter().copied().filter(|x| !cb.contains(x)).collect();
                let only_b: Vec<Id> = cb.iter().copied().filter(|y| !ca.contains(y)).collect();
                only_a.first().copied().zip(only_b.first().copied())
            } else {
                ca.into_iter().zip(cb).find(|(x, y)| x != y)
            };
            match pair {
                Some((x, y)) => first_difference(s, x, y),
                None => (a, b),
            }
        }
        _ => (a, b),
    }
}

/// A branch condition on computed values.
#[derive(Clone, Debug, PartialEq)]
enum Cond {
    Const(bool),
    Lt(Id, Id),
    Le(Id, Id),
    Eq(Id, Id),
    Not(Box<Cond>),
    /// `if c { a } else { b }` for boolean `a`, `b` (short-circuit operators).
    If(Box<Cond>, Box<Cond>, Box<Cond>),
    /// An untracked flag: both branches must agree on every computed value.
    Unknown,
}

fn select(s: &mut Store, cond: &Cond, x: Id, y: Id) -> Id {
    if x == y {
        return x;
    }
    match cond {
        Cond::Const(b) => {
            if *b {
                x
            } else {
                y
            }
        }
        &Cond::Lt(a, b) => s.sel(a, b, x, y),
        &Cond::Le(a, b) => s.sel(b, a, y, x),
        &Cond::Eq(a, z) if z == s.zero() && s.nonneg(a) => {
            let (na, zero) = (s.neg(a), s.zero());
            s.sel(na, zero, y, x)
        }
        Cond::Not(c) => select(s, c, y, x),
        Cond::If(c, a, b) => {
            let xa = select(s, a, x, y);
            let xb = select(s, b, x, y);
            select(s, c, xa, xb)
        }
        Cond::Eq(a, b) => panic!(
            "no exact encoding of {} == {}",
            s.show(*a, 3),
            s.show(*b, 3)
        ),
        Cond::Unknown => panic!("a branch on an untracked flag changes a computed value"),
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Scalar(Id),
    Vector(Vec<Id>),
    /// Columns.
    Matrix(Vec<Vec<Id>>),
    /// Structs and arrays.
    Struct(Vec<Value>),
    Int(i64),
    /// Integer vectors, such as the loop counter naga's SPIR-V writer adds.
    Ints(Vec<i64>),
    Bool(Cond),
    /// A flag the Lean models do not track (`Metric.valid`).
    Unknown,
}

impl Value {
    fn scalar(self) -> Id {
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
            Value::Bool(c) => c,
            Value::Unknown => Cond::Unknown,
            v => panic!("expected bool, got {v:?}"),
        }
    }
    /// The floating-point components; flags are dropped.
    fn flatten(self, out: &mut Vec<Id>) {
        match self {
            Value::Scalar(t) => out.push(t),
            Value::Vector(v) => out.extend(v),
            Value::Matrix(cols) => cols.into_iter().for_each(|c| out.extend(c)),
            Value::Struct(fields) => fields.into_iter().for_each(|f| f.flatten(out)),
            // Flags, including booleans the SPIR-V reader stores as integers.
            Value::Bool(_) | Value::Unknown | Value::Int(_) | Value::Ints(_) => {}
        }
    }
    fn get(&self, path: &[usize]) -> Value {
        let Some((&i, rest)) = path.split_first() else {
            return self.clone();
        };
        match self {
            Value::Struct(f) => f[i].get(rest),
            Value::Matrix(m) => Value::Vector(m[i].clone()).get(rest),
            Value::Vector(v) if rest.is_empty() => Value::Scalar(v[i]),
            Value::Ints(v) if rest.is_empty() => Value::Int(v[i]),
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
            Value::Ints(v) if rest.is_empty() => v[i] = new.int(),
            v => panic!("path {path:?} into {v:?}"),
        }
    }
}

fn select_value(s: &mut Store, cond: &Cond, a: Value, b: Value) -> Value {
    use Value::*;
    let pick = |s: &mut Store, x: Vec<Id>, y: Vec<Id>| -> Vec<Id> {
        x.into_iter()
            .zip(y)
            .map(|(x, y)| select(s, cond, x, y))
            .collect()
    };
    match (a, b) {
        (a, b) if a == b => a,
        (a, b) if matches!(cond, Cond::Const(_)) => {
            if *cond == Cond::Const(true) {
                a
            } else {
                b
            }
        }
        (Scalar(x), Scalar(y)) => Scalar(select(s, cond, x, y)),
        (Vector(x), Vector(y)) => Vector(pick(s, x, y)),
        (Matrix(x), Matrix(y)) => {
            Matrix(x.into_iter().zip(y).map(|(x, y)| pick(s, x, y)).collect())
        }
        (Struct(x), Struct(y)) => Struct(
            x.into_iter()
                .zip(y)
                .map(|(x, y)| select_value(s, cond, x, y))
                .collect(),
        ),
        (Unknown, Bool(_) | Unknown) | (Bool(_), Unknown) => Unknown,
        (Bool(x), Bool(y)) => match cond {
            Cond::Const(true) => Bool(x),
            Cond::Const(false) => Bool(y),
            c => Bool(Cond::If(Box::new(c.clone()), Box::new(x), Box::new(y))),
        },
        (a, b) => panic!("cannot merge {a:?} and {b:?}"),
    }
}

fn zero(s: &mut Store, module: &Module, ty: Handle<naga::Type>) -> Value {
    let z = s.zero();
    match &module.types[ty].inner {
        TypeInner::Scalar(sc) => match sc.kind {
            ScalarKind::Float => Value::Scalar(z),
            ScalarKind::Bool => Value::Bool(Cond::Const(false)),
            _ => Value::Int(0),
        },
        TypeInner::Vector { size, scalar } if scalar.kind != ScalarKind::Float => {
            Value::Ints(vec![0; *size as usize])
        }
        TypeInner::Vector { size, .. } => Value::Vector(vec![z; *size as usize]),
        TypeInner::Matrix { columns, rows, .. } => {
            Value::Matrix(vec![vec![z; *rows as usize]; *columns as usize])
        }
        TypeInner::Struct { members, .. } => {
            Value::Struct(members.iter().map(|m| zero(s, module, m.ty)).collect())
        }
        TypeInner::Array {
            base,
            size: ArraySize::Constant(n),
            ..
        } => Value::Struct(vec![zero(s, module, *base); n.get() as usize]),
        t => panic!("unsupported zero value {t:?}"),
    }
}

/// Applies `f` lane by lane, broadcasting scalars against vectors.
fn lanes(s: &mut Store, args: Vec<Value>, f: impl Fn(&mut Store, Vec<Id>) -> Id) -> Value {
    let width = args.iter().find_map(|a| match a {
        Value::Vector(v) => Some(v.len()),
        _ => None,
    });
    let lane = |i: usize| -> Vec<Id> {
        args.iter()
            .map(|a| match a {
                Value::Scalar(t) => *t,
                Value::Vector(v) => v[i],
                a => panic!("lane of {a:?}"),
            })
            .collect()
    };
    match width {
        None => Value::Scalar(f(s, lane(0))),
        Some(n) => Value::Vector((0..n).map(|i| f(s, lane(i))).collect()),
    }
}

fn binary(s: &mut Store, op: BinaryOperator, a: Value, b: Value) -> Value {
    use BinaryOperator as B;
    use Value::*;
    match (op, a, b) {
        (B::Add, Int(x), Int(y)) => Int(x + y),
        (B::Subtract, Int(x), Int(y)) => Int(x - y),
        (B::Less, Int(x), Int(y)) => Bool(Cond::Const(x < y)),
        (B::LessEqual, Int(x), Int(y)) => Bool(Cond::Const(x <= y)),
        (B::Greater, Int(x), Int(y)) => Bool(Cond::Const(x > y)),
        (B::GreaterEqual, Int(x), Int(y)) => Bool(Cond::Const(x >= y)),
        (B::Equal, Int(x), Int(y)) => Bool(Cond::Const(x == y)),
        (B::NotEqual, Int(x), Int(y)) => Bool(Cond::Const(x != y)),
        // Lane-wise integer equality, as 0/1 lanes for `all`/`any`.
        (B::Equal, Ints(x), Ints(y)) => {
            Ints(x.iter().zip(&y).map(|(a, b)| i64::from(a == b)).collect())
        }
        (B::Subtract, Ints(x), Ints(y)) => Ints(x.iter().zip(&y).map(|(a, b)| a - b).collect()),
        (B::LogicalAnd | B::LogicalOr, Unknown, _) | (B::LogicalAnd | B::LogicalOr, _, Unknown) => {
            Unknown
        }
        (
            B::Less | B::LessEqual | B::Greater | B::GreaterEqual | B::Equal,
            Scalar(x),
            Scalar(y),
        ) => Bool(match op {
            B::Less => Cond::Lt(x, y),
            B::Greater => Cond::Lt(y, x),
            B::LessEqual => Cond::Le(x, y),
            B::GreaterEqual => Cond::Le(y, x),
            _ => Cond::Eq(x, y),
        }),
        (B::Multiply, Matrix(m), Vector(v)) => {
            // Row r of M v sums M[c][r] v[c] over columns c.
            let rows = m[0].len();
            Vector(
                (0..rows)
                    .map(|r| {
                        let terms = m.iter().zip(&v).map(|(col, &x)| s.mul(col[r], x)).collect();
                        s.sum(terms)
                    })
                    .collect(),
            )
        }
        (op, a, b) => {
            let node = move |s: &mut Store, x: Id, y: Id| match op {
                B::Add => s.add(x, y),
                B::Subtract => s.sub(x, y),
                B::Multiply => s.mul(x, y),
                B::Divide => s.div(x, y),
                op => panic!("unsupported operator {op:?}"),
            };
            match (a, b) {
                (Matrix(x), Matrix(y)) if op != B::Multiply => Matrix(
                    x.into_iter()
                        .zip(y)
                        .map(|(a, b)| a.into_iter().zip(b).map(|(x, y)| node(s, x, y)).collect())
                        .collect(),
                ),
                (Matrix(m), Scalar(k)) => Matrix(
                    m.into_iter()
                        .map(|c| c.into_iter().map(|y| node(s, y, k)).collect())
                        .collect(),
                ),
                (Scalar(k), Matrix(m)) => Matrix(
                    m.into_iter()
                        .map(|c| c.into_iter().map(|y| node(s, k, y)).collect())
                        .collect(),
                ),
                (a @ (Scalar(_) | Vector(_)), b @ (Scalar(_) | Vector(_))) => {
                    lanes(s, vec![a, b], |s, t| node(s, t[0], t[1]))
                }
                (a, b) => panic!("unsupported operands {op:?} {a:?} {b:?}"),
            }
        }
    }
}

fn dot(s: &mut Store, a: &[Id], b: &[Id]) -> Id {
    let terms = a.iter().zip(b).map(|(&x, &y)| s.mul(x, y)).collect();
    s.sum(terms)
}

/// WGSL's inherited `tanh`: `sinh(x)/cosh(x)` with `sinh`, `cosh` from `exp`
/// (`WgslPlasma.tanhInh`, reading its argument as input 0).
fn tanh_inherited(s: &mut Store) -> Id {
    let x = s.input(0);
    let ex = s.f("exp", vec![x]);
    let nx = s.neg(x);
    let enx = s.f("exp", vec![nx]);
    let half = s.dyadic(1, -1);
    let (d, m) = (s.sub(ex, enx), s.add(ex, enx));
    let (sinh, cosh) = (s.mul(d, half), s.mul(m, half));
    s.div(sinh, cosh)
}

fn math(s: &mut Store, fun: MathFunction, mut args: Vec<Value>) -> Value {
    use MathFunction as M;
    let vector = |v: Value| match v {
        Value::Vector(v) => v,
        v => panic!("expected vector, got {v:?}"),
    };
    let name = match fun {
        M::Max => "max",
        M::Min => "min",
        M::Abs => "abs",
        M::Sqrt => "sqrt",
        M::InverseSqrt => "invsqrt",
        M::Exp => "exp",
        M::Exp2 => "exp2",
        M::Log => "log",
        M::Log2 => "log2",
        _ => "",
    };
    if !name.is_empty() {
        return lanes(s, args, |s, t| s.f(name, t));
    }
    match fun {
        M::Dot => {
            let b = vector(args.pop().unwrap());
            Value::Scalar(dot(s, &vector(args.pop().unwrap()), &b))
        }
        M::Mix => lanes(s, args, |s, t| {
            let one = s.dyadic(1, 0);
            let rest = s.sub(one, t[2]);
            let (a, b) = (s.mul(t[0], rest), s.mul(t[1], t[2]));
            s.add(a, b)
        }),
        M::SmoothStep => lanes(s, args, |s, t| {
            let (num, den) = (s.sub(t[2], t[0]), s.sub(t[1], t[0]));
            let q = s.div(num, den);
            let (zero, one) = (s.zero(), s.dyadic(1, 0));
            let lo = s.f("max", vec![q, zero]);
            let u = s.f("min", vec![lo, one]);
            let (two, three) = (s.dyadic(1, 1), s.dyadic(3, 0));
            let uu = s.mul(u, u);
            let tu = s.mul(two, u);
            let k = s.sub(three, tu);
            s.mul(uu, k)
        }),
        M::Clamp => lanes(s, args, |s, t| {
            let lo = s.f("max", vec![t[0], t[1]]);
            s.f("min", vec![lo, t[2]])
        }),
        M::Length => {
            let v = vector(args.pop().unwrap());
            let d = dot(s, &v, &v);
            Value::Scalar(s.f("sqrt", vec![d]))
        }
        M::Normalize => {
            let v = vector(args.pop().unwrap());
            let d = dot(s, &v, &v);
            let norm = s.f("sqrt", vec![d]);
            Value::Vector(v.into_iter().map(|x| s.div(x, norm)).collect())
        }
        M::Cross => {
            let b = vector(args.pop().unwrap());
            let a = vector(args.pop().unwrap());
            let mut term = |i: usize, j: usize| {
                let (p, q) = (s.mul(a[i], b[j]), s.mul(a[j], b[i]));
                s.sub(p, q)
            };
            Value::Vector(vec![term(1, 2), term(2, 0), term(0, 1)])
        }
        // pow(x, y) is inherited from exp2(y * log2(x)) (`WgslPlasma.pow`).
        M::Pow => lanes(s, args, |s, t| {
            let x0 = s.input(0);
            let l = s.f("log2", vec![x0]);
            let yl = s.mul(t[1], l);
            let inner = s.f("exp2", vec![yl]);
            s.f("inh", vec![inner, t[0]])
        }),
        M::Tanh => lanes(s, args, |s, t| {
            let inherited = tanh_inherited(s);
            s.f("tanh", vec![inherited, t[0]])
        }),
        fun => panic!("unsupported builtin {fun:?}"),
    }
}

/// Constructors, component access and arithmetic, shared by global and
/// function expressions; `None` for the cases that need a function frame.
fn common(
    s: &mut Store,
    module: &Module,
    e: &Expression,
    sub: &mut dyn FnMut(&mut Store, Handle<Expression>) -> Value,
) -> Option<Value> {
    Some(match e {
        Expression::Literal(Literal::F32(x)) => Value::Scalar(s.f32(*x)),
        Expression::Literal(Literal::U32(x)) => Value::Int((*x).into()),
        Expression::Literal(Literal::I32(x)) => Value::Int((*x).into()),
        Expression::Literal(Literal::Bool(b)) => Value::Bool(Cond::Const(*b)),
        Expression::Constant(c) => global(s, module, module.constants[*c].init),
        Expression::ZeroValue(ty) => zero(s, module, *ty),
        Expression::Compose { ty, components } => {
            let parts: Vec<Value> = components.iter().map(|c| sub(s, *c)).collect();
            match &module.types[*ty].inner {
                TypeInner::Vector { scalar, .. } if scalar.kind != ScalarKind::Float => {
                    Value::Ints(parts.into_iter().map(Value::int).collect())
                }
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
            Value::Vector(vec![sub(s, *value).scalar(); *size as usize])
        }
        Expression::AccessIndex { base, index } => sub(s, *base).get(&[*index as usize]),
        Expression::Access { base, index } => {
            let i = sub(s, *index).int() as usize;
            sub(s, *base).get(&[i])
        }
        Expression::Swizzle {
            size,
            vector,
            pattern,
        } => match sub(s, *vector) {
            Value::Vector(v) => Value::Vector(
                pattern[..*size as usize]
                    .iter()
                    .map(|c| v[*c as usize])
                    .collect(),
            ),
            v => panic!("swizzle of {v:?}"),
        },
        Expression::Unary {
            op: naga::UnaryOperator::Negate,
            expr,
        } => {
            let v = sub(s, *expr);
            lanes(s, vec![v], |s, t| s.neg(t[0]))
        }
        Expression::Unary {
            op: naga::UnaryOperator::LogicalNot,
            expr,
        } => Value::Bool(match sub(s, *expr).cond() {
            Cond::Const(b) => Cond::Const(!b),
            Cond::Unknown => Cond::Unknown,
            c => Cond::Not(Box::new(c)),
        }),
        Expression::Binary { op, left, right } => {
            let (l, r) = (sub(s, *left), sub(s, *right));
            binary(s, *op, l, r)
        }
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
                .map(|a| sub(s, a))
                .collect();
            math(s, *fun, args)
        }
        // `all`/`any` only feed flags here; a branch on them that changed a
        // computed value would fail as an untracked-flag branch.
        Expression::Relational { fun, argument } => match sub(s, *argument) {
            Value::Bool(Cond::Const(b)) => Value::Bool(Cond::Const(b)),
            Value::Ints(lanes) => Value::Bool(Cond::Const(match fun {
                naga::RelationalFunction::All => lanes.iter().all(|&l| l != 0),
                _ => lanes.iter().any(|&l| l != 0),
            })),
            _ => Value::Unknown,
        },
        Expression::Select {
            condition,
            accept,
            reject,
        } => {
            let c = sub(s, *condition).cond();
            let (a, b) = (sub(s, *accept), sub(s, *reject));
            select_value(s, &c, a, b)
        }
        _ => return None,
    })
}

fn global(s: &mut Store, module: &Module, h: Handle<Expression>) -> Value {
    let e = &module.global_expressions[h];
    common(s, module, e, &mut |s, h| global(s, module, h))
        .unwrap_or_else(|| panic!("unsupported constant {e:?}"))
}

/// A call the Lean model treats as a primitive or an input.
type Primitive = fn(&mut Store, Vec<Value>) -> Value;

/// What a kernel is evaluated on, and the parts of it the Lean model
/// abstracts.
#[derive(Default)]
struct Env {
    args: Vec<Value>,
    globals: HashMap<String, Value>,
    /// Calls whose results the Lean model reads as inputs or primitives.
    opaque_calls: HashMap<&'static str, Primitive>,
    /// Values the Lean model reads as inputs: a computed value equal to the
    /// expected expressions is replaced, and each must be found.
    lets: Vec<(Vec<Id>, Value, std::cell::Cell<bool>)>,
    /// Values the model assumes positive; the other branch is outside it.
    positive: Vec<Id>,
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

type Place = (Handle<naga::LocalVariable>, Vec<usize>);

impl<'a> Frame<'a> {
    /// The local variable and component path a pointer expression names.
    fn place(&mut self, s: &mut Store, h: Handle<Expression>) -> Option<Place> {
        match self.func.expressions[h] {
            Expression::LocalVariable(l) => Some((l, vec![])),
            Expression::AccessIndex { base, index } => {
                let mut p = self.place(s, base)?;
                p.1.push(index as usize);
                Some(p)
            }
            Expression::Access { base, index } => {
                let mut p = self.place(s, base)?;
                p.1.push(self.eval(s, index).int() as usize);
                Some(p)
            }
            _ => None,
        }
    }

    fn eval(&mut self, s: &mut Store, h: Handle<Expression>) -> Value {
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
            Expression::Load { pointer } => match self.place(s, *pointer) {
                Some((l, path)) => self.locals[&l].get(&path),
                None => self.eval(s, *pointer),
            },
            e => {
                let module = self.module;
                common(s, module, e, &mut |s, h| self.eval(s, h))
                    .unwrap_or_else(|| panic!("unsupported expression {e:?}"))
            }
        }
    }

    fn emit(&mut self, s: &mut Store, h: Handle<Expression>) {
        // Pointers into locals are resolved by the loads and stores that use them.
        if self.place(s, h).is_some() {
            return;
        }
        // A loop re-emits its body's expressions; each iteration recomputes them.
        self.emitted.remove(&h);
        let mut v = self.eval(s, h);
        if self.top && matches!(v, Value::Vector(_) | Value::Scalar(_)) {
            let mut computed = Vec::new();
            v.clone().flatten(&mut computed);
            if let Some((_, replacement, found)) =
                self.env.lets.iter().find(|(e, _, _)| *e == computed)
            {
                found.set(true);
                v = replacement.clone();
            }
        }
        self.emitted.insert(h, v);
    }

    fn resolve(&self, s: &mut Store, c: Cond) -> Cond {
        let zero = s.zero();
        let positive = |t: Id| self.env.positive.contains(&t);
        match c {
            Cond::Le(a, z) if z == zero && positive(a) => Cond::Const(false),
            Cond::Lt(z, a) if z == zero && positive(a) => Cond::Const(true),
            c => c,
        }
    }

    /// Statements that never fork; `None` for those `exec` handles.
    fn simple(&mut self, s: &mut Store, statement: &'a Statement) -> Option<Flow> {
        match statement {
            Statement::Emit(range) => range.clone().for_each(|h| self.emit(s, h)),
            Statement::Store { pointer, value } => {
                let (l, path) = self.place(s, *pointer).unwrap_or_else(|| {
                    panic!("store through {:?}", self.func.expressions[*pointer])
                });
                let v = self.eval(s, *value);
                self.locals.get_mut(&l).unwrap().set(&path, v);
            }
            Statement::Call {
                function,
                arguments,
                result,
            } => {
                let args = arguments.iter().map(|a| self.eval(s, *a)).collect();
                let callee = &self.module.functions[*function];
                let name = callee.name.as_deref().unwrap_or_default();
                let v = match self.env.opaque_calls.get(name) {
                    Some(f) => f(s, args),
                    None => run(s, self.module, callee, args, self.env, false),
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
                if let Flow::Break = self.straight(s, body) {
                    break;
                }
                self.straight(s, continuing);
                if let Some(c) = break_if {
                    let Cond::Const(stop) = self.eval(s, *c).cond() else {
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

    /// Runs `accept` and `reject` without returning and merges every local:
    /// the branches of an `if` that falls through.
    fn merge(&mut self, s: &mut Store, c: Cond, accept: &'a naga::Block, reject: &'a naga::Block) {
        let mut other = self.clone();
        let (fa, fb) = (self.straight(s, accept), other.straight(s, reject));
        assert!(
            matches!((fa, fb), (Flow::Next, Flow::Next)),
            "loop exit inside a branch on {c:?}"
        );
        for (l, v) in std::mem::take(&mut self.locals) {
            let w = other.locals.remove(&l).unwrap();
            let merged = select_value(s, &c, v, w);
            self.locals.insert(l, merged);
        }
    }

    /// Statements without `return`; branches on computed values merge.
    fn straight(&mut self, s: &mut Store, block: &'a naga::Block) -> Flow {
        for statement in block.iter() {
            let flow = match statement {
                Statement::Block(b) => self.straight(s, b),
                Statement::If {
                    condition,
                    accept,
                    reject,
                } => {
                    let c = self.eval(s, *condition).cond();
                    match self.resolve(s, c) {
                        Cond::Const(b) => self.straight(s, if b { accept } else { reject }),
                        c => {
                            self.merge(s, c, accept, reject);
                            Flow::Next
                        }
                    }
                }
                st => self
                    .simple(s, st)
                    .unwrap_or_else(|| panic!("unsupported statement in loop {st:?}")),
            };
            if !matches!(flow, Flow::Next) {
                return flow;
            }
        }
        Flow::Next
    }

    /// Runs the statements on `stack` (innermost block last) to a `return`.
    fn exec(&mut self, s: &mut Store, mut stack: Vec<&'a [Statement]>) -> Value {
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
                Statement::Return { value } => {
                    return self.eval(s, value.expect("void return"));
                }
                Statement::If {
                    condition,
                    accept,
                    reject,
                } => {
                    let c = self.eval(s, *condition).cond();
                    match self.resolve(s, c) {
                        Cond::Const(b) => stack.push(if b { accept } else { reject }),
                        c if !returns(accept) && !returns(reject) => {
                            self.merge(s, c, accept, reject)
                        }
                        c => {
                            let mut other = self.clone();
                            let mut other_stack = stack.clone();
                            other_stack.push(reject);
                            stack.push(accept);
                            let a = self.exec(s, stack);
                            let b = other.exec(s, other_stack);
                            return select_value(s, &c, a, b);
                        }
                    }
                }
                st => match self.simple(s, st) {
                    Some(Flow::Next) => {}
                    _ => panic!("unsupported statement {st:?}"),
                },
            }
        }
    }
}

/// Whether a block can `return`; such branches fork the rest of the function.
fn returns(block: &naga::Block) -> bool {
    block.iter().any(|st| match st {
        Statement::Return { .. } => true,
        Statement::Block(b) => returns(b),
        Statement::If { accept, reject, .. } => returns(accept) || returns(reject),
        Statement::Loop {
            body, continuing, ..
        } => returns(body) || returns(continuing),
        _ => false,
    })
}

fn run(
    s: &mut Store,
    module: &Module,
    func: &naga::Function,
    args: Vec<Value>,
    env: &Env,
    top: bool,
) -> Value {
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
            Some(e) => frame.eval(s, e),
            None => zero(s, module, var.ty),
        };
        frame.locals.insert(l, v);
    }
    frame.exec(s, vec![&func.body])
}

/// Marks inputs the Lean model does not read; any use shows up as a mismatch.
const UNUSED: u32 = u32::MAX;

fn opaque(s: &mut Store, module: &Module, ty: Handle<naga::Type>) -> Value {
    let u = s.input(UNUSED);
    match &module.types[ty].inner {
        TypeInner::Scalar(sc) if sc.kind == ScalarKind::Bool => Value::Unknown,
        TypeInner::Scalar(_) => Value::Scalar(u),
        TypeInner::Vector { size, .. } => Value::Vector(vec![u; *size as usize]),
        TypeInner::Matrix { columns, rows, .. } => {
            Value::Matrix(vec![vec![u; *rows as usize]; *columns as usize])
        }
        TypeInner::Struct { members, .. } => {
            Value::Struct(members.iter().map(|m| opaque(s, module, m.ty)).collect())
        }
        t => panic!("unsupported argument type {t:?}"),
    }
}

/// Lean's `inv i j = input (base + 4 i + j)` reads row `i`, column `j`;
/// WGSL `m[j][i]` is column `j`, row `i`.
fn matrix(s: &mut Store, base: u32) -> Value {
    Value::Matrix(
        (0..4)
            .map(|c| (0..4).map(|r| s.input(base + 4 * r + c)).collect())
            .collect(),
    )
}

fn vector(s: &mut Store, base: u32, n: u32) -> Value {
    Value::Vector((0..n).map(|i| s.input(base + i)).collect())
}

fn scalar(s: &mut Store, i: u32) -> Value {
    Value::Scalar(s.input(i))
}

/// A struct whose named members carry Lean input indices or fixed values.
fn record(
    s: &mut Store,
    module: &Module,
    ty: Handle<naga::Type>,
    fields: Vec<(&str, Value)>,
) -> Value {
    let TypeInner::Struct { members, .. } = &module.types[ty].inner else {
        panic!("expected a struct");
    };
    Value::Struct(
        members
            .iter()
            .map(|m| {
                let name = m.name.as_deref().unwrap_or_default();
                match fields.iter().find(|(n, _)| *n == name) {
                    Some((_, v)) => v.clone(),
                    None => opaque(s, module, m.ty),
                }
            })
            .collect(),
    )
}

fn global_record(
    s: &mut Store,
    module: &Module,
    name: &str,
    fields: Vec<(&str, Value)>,
) -> (String, Value) {
    let (_, var) = module
        .global_variables
        .iter()
        .find(|(_, g)| g.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no global {name}"));
    // naga's SPIR-V writer wraps a uniform struct in a one-member block.
    let value = match &module.types[var.ty].inner {
        TypeInner::Struct { members, .. } if members.len() == 1 && members[0].name.is_none() => {
            Value::Struct(vec![record(s, module, members[0].ty, fields)])
        }
        _ => record(s, module, var.ty, fields),
    };
    (name.to_string(), value)
}

fn function<'m>(module: &'m Module, name: &str) -> &'m naga::Function {
    module
        .functions
        .iter()
        .map(|(_, f)| f)
        .find(|f| f.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no function {name}"))
}

struct Ctx<'a> {
    module: &'a Module,
    func: &'a naga::Function,
    fixture: &'a Fixture,
}

/// Input layout of `BlackHole.WgslGeodesic`: `inv` 0–15, `dx` 16–31,
/// `dy` 32–47, `dz` 48–63, momentum 64–67, screen 68–71.
fn geodesic_rhs_setup(s: &mut Store, cx: &Ctx) -> Env {
    let fields = vec![("p", vector(s, 64, 4)), ("screen", vector(s, 68, 4))];
    let ray = record(s, cx.module, cx.func.arguments[0].ty, fields);
    let fields = vec![
        ("inv", matrix(s, 0)),
        ("dx", matrix(s, 16)),
        ("dy", matrix(s, 32)),
        ("dz", matrix(s, 48)),
    ];
    let metric = record(s, cx.module, cx.func.arguments[1].ty, fields);
    Env {
        args: vec![ray, metric],
        ..Env::default()
    }
}

fn scalar_setup(s: &mut Store, _: &Ctx) -> Env {
    Env {
        args: vec![scalar(s, 0)],
        ..Env::default()
    }
}

/// Every channel reads input 0, matching the one-channel Lean model.
fn tonemap_setup(s: &mut Store, _: &Ctx) -> Env {
    Env {
        args: vec![Value::Vector(vec![s.input(0); 3])],
        ..Env::default()
    }
}

/// Stokes vector 0–3 with `polarization_view == 2` (the hue view).
fn polarization_setup(s: &mut Store, cx: &Ctx) -> Env {
    let cam = global_record(
        s,
        cx.module,
        "cam",
        vec![("polarization_view", Value::Int(2))],
    );
    Env {
        args: vec![vector(s, 0, 4)],
        globals: HashMap::from([cam]),
        ..Env::default()
    }
}

/// `WgslScreen.spatialUnit` with `v` at inputs 100–102 and `gamma` from the
/// metric `g` (entry `4 i + j`): `gamma[c][r] = g[c+1][r+1]`.
fn spatial_unit_setup(s: &mut Store, _: &Ctx) -> Env {
    let gamma = Value::Matrix(
        (0..3)
            .map(|c| (0..3).map(|r| s.input(4 * (r + 1) + c + 1)).collect())
            .collect(),
    );
    Env {
        args: vec![vector(s, 100, 3), gamma],
        ..Env::default()
    }
}

/// Input layout of `BlackHole.WgslAddKerr`: `x` 0–2, mass 6, incoming `g`
/// 8–23, `inv` 24–39, `dx/dy/dz` 40–87, clearance 88. The model reads the
/// scaled spin `a` as inputs 3–5 and `kerr_radius(x, a)` as input 7; the
/// computed `a` must equal `WgslAddKerr.spinScale` (spin 200–202, mass 6).
/// The model covers `mass > 0`; `mass <= 0` returns the input metric.
fn add_kerr_setup(s: &mut Store, cx: &Ctx) -> Env {
    let fields = vec![
        ("g", matrix(s, 8)),
        ("inv", matrix(s, 24)),
        ("dx", matrix(s, 40)),
        ("dy", matrix(s, 56)),
        ("dz", matrix(s, 72)),
        ("clearance", scalar(s, 88)),
    ];
    let base = record(s, cx.module, cx.func.arguments[0].ty, fields);
    let spin_input = |i: u32| if i < 3 { 200 + i } else { 6 };
    let spin_scale = lean(s, cx.fixture, "spin_scale", &spin_input);
    let a = vector(s, 3, 3);
    let mass = s.input(6);
    Env {
        args: vec![base, vector(s, 0, 3), scalar(s, 6), vector(s, 200, 3)],
        opaque_calls: HashMap::from([(
            "kerr_radius",
            (|s: &mut Store, _| scalar(s, 7)) as Primitive,
        )]),
        lets: vec![(spin_scale, a, Default::default())],
        positive: vec![mass],
        ..Env::default()
    }
}

/// `screen_frame` with `WgslScreen`'s inputs: `g` 0–15, `inv` 16–31,
/// momentum 32–35, screen 36–39.
fn screen_frame_setup(s: &mut Store, cx: &Ctx) -> Env {
    let fields = vec![("p", vector(s, 32, 4)), ("screen", vector(s, 36, 4))];
    let ray = record(s, cx.module, cx.func.arguments[0].ty, fields);
    let fields = vec![("g", matrix(s, 0)), ("inv", matrix(s, 16))];
    let metric = record(s, cx.module, cx.func.arguments[1].ty, fields);
    Env {
        args: vec![ray, metric],
        ..Env::default()
    }
}

fn sincos(s: &mut Store, mut args: Vec<Value>) -> Value {
    let x = args.pop().unwrap().scalar();
    Value::Vector(vec![s.f("sinS", vec![x]), s.f("cosS", vec![x])])
}

/// `sample_plasma` with `WgslPlasma`'s inputs (`screen_frame`'s, then `pos`
/// 40–42, disk 43–49 and 53–55, camera 50–52) for one disk model of a
/// single, non-binary source.
fn plasma_setup(s: &mut Store, cx: &Ctx, model: i64) -> Env {
    let fields = vec![
        ("pos", vector(s, 40, 3)),
        ("p", vector(s, 32, 4)),
        ("screen", vector(s, 36, 4)),
    ];
    let ray = record(s, cx.module, cx.func.arguments[0].ty, fields);
    let fields = vec![("g", matrix(s, 0)), ("inv", matrix(s, 16))];
    let metric = record(s, cx.module, cx.func.arguments[1].ty, fields);
    let disk_fields = [
        ("r1", 43),
        ("r2", 44),
        ("h_thin", 45),
        ("h_hot", 46),
        ("spin", 47),
        ("isco_r", 48),
        ("r_trunc", 49),
        ("r_bp", 53),
        ("tilt_deg", 54),
        ("twist_deg", 55),
    ];
    let mut fields: Vec<(&str, Value)> = disk_fields
        .iter()
        .map(|&(n, i)| (n, scalar(s, i)))
        .collect();
    fields.extend([
        ("model", Value::Int(model)),
        ("binary_enabled", Value::Int(0)),
    ]);
    let disk = global_record(s, cx.module, "disk", fields);
    let fields = vec![
        ("frequency_ghz", scalar(s, 50)),
        ("faraday_depth", scalar(s, 51)),
        ("conversion_depth", scalar(s, 52)),
    ];
    let cam = global_record(s, cx.module, "cam", fields);
    Env {
        args: vec![ray, metric],
        globals: HashMap::from([disk, cam]),
        opaque_calls: HashMap::from([("sincos", sincos as Primitive)]),
        ..Env::default()
    }
}

fn thin_setup(s: &mut Store, cx: &Ctx) -> Env {
    plasma_setup(s, cx, 0)
}
fn truncated_setup(s: &mut Store, cx: &Ctx) -> Env {
    plasma_setup(s, cx, 1)
}
fn slim_setup(s: &mut Store, cx: &Ctx) -> Env {
    plasma_setup(s, cx, 2)
}
fn warped_setup(s: &mut Store, cx: &Ctx) -> Env {
    plasma_setup(s, cx, 3)
}

/// `kerr_radius(x, a)` with `x` inputs 0–2 and `a` inputs 3–5.
fn kerr_radius_setup(s: &mut Store, _: &Ctx) -> Env {
    Env {
        args: vec![vector(s, 0, 3), vector(s, 3, 3)],
        ..Env::default()
    }
}

/// `atan2_arith(y, x)` with `y` input 0 and `x` input 1.
fn atan2_setup(s: &mut Store, _: &Ctx) -> Env {
    Env {
        args: vec![scalar(s, 0), scalar(s, 1)],
        ..Env::default()
    }
}

type Setup = fn(&mut Store, &Ctx) -> Env;

/// Where the compared IR comes from: naga's WGSL front end, or the SPIR-V
/// that naga's backend writes from it, read back by naga's SPIR-V front end.
/// The second checks the SPIR-V backend for these kernels, trusting only the
/// independent SPIR-V reader.
#[derive(Debug, Clone, Copy)]
enum Stage {
    Wgsl,
    Spirv,
}

impl Stage {
    fn module(self) -> Module {
        let source = common::compile_wesl(include_str!("../assets/shaders/geodesic.wesl"));
        let module = naga::front::wgsl::parse_str(&source).expect("geodesic.wesl parses");
        if let Stage::Wgsl = self {
            return module;
        }
        let info = naga::valid::Validator::new(
            naga::valid::ValidationFlags::all(),
            naga::valid::Capabilities::all(),
        )
        .validate(&module)
        .expect("geodesic.wesl validates");
        let options = naga::back::spv::Options {
            flags: naga::back::spv::WriterFlags::DEBUG,
            ..Default::default()
        };
        let words = naga::back::spv::write_vec(&module, &info, &options, None).expect("SPIR-V");
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        naga::front::spv::parse_u8_slice(&bytes, &naga::front::spv::Options::default())
            .expect("naga reads its SPIR-V")
    }
}

#[rstest::rstest]
#[case::geodesic_rhs("geodesic_rhs", geodesic_rhs_setup as Setup)]
#[case::atan_poly("atan_poly", scalar_setup as Setup)]
#[case::tonemap("tonemap", tonemap_setup as Setup)]
#[case::heatmap_color("heatmap_color", scalar_setup as Setup)]
#[case::polarization_color("polarization_color", polarization_setup as Setup)]
#[case::spatial_unit("spatial_unit", spatial_unit_setup as Setup)]
#[case::add_kerr("add_kerr", add_kerr_setup as Setup)]
#[case::screen_frame("screen_frame", screen_frame_setup as Setup)]
#[case::plasma_thin("sample_plasma.0", thin_setup as Setup)]
#[case::plasma_truncated("sample_plasma.1", truncated_setup as Setup)]
#[case::plasma_slim("sample_plasma.2", slim_setup as Setup)]
#[case::plasma_warped("sample_plasma.3", warped_setup as Setup)]
#[case::atan2_arith("atan2_arith", atan2_setup as Setup)]
#[case::kerr_radius("kerr_radius", kerr_radius_setup as Setup)]
fn naga_ir_matches_lean_model(
    #[case] model: &str,
    #[case] setup: Setup,
    #[values(Stage::Wgsl, Stage::Spirv)] stage: Stage,
) {
    let name = model.split('.').next().unwrap();
    let module = stage.module();
    let func = function(&module, name);
    let fixture = fixture();
    let cx = Ctx {
        module: &module,
        func,
        fixture: &fixture,
    };
    let mut s = Store::default();
    let env = setup(&mut s, &cx);
    let mut out = Vec::new();
    run(&mut s, &module, func, env.args.clone(), &env, true).flatten(&mut out);
    assert!(
        env.lets.iter().all(|(_, _, found)| found.get()),
        "{model}: a value the model reads as an input was not computed"
    );
    let expected = lean(&mut s, &fixture, model, &|i| i);
    compare(&s, &out, &expected, model);
}

#[test]
fn fixture_lists_the_checked_kernels() {
    let mut counts: Vec<(String, usize)> = fixture()
        .into_iter()
        .map(|(name, rows)| (name, rows.len()))
        .collect();
    counts.sort();
    let expected = [
        ("add_kerr", 81),
        ("atan2_arith", 1),
        ("atan2_arith:let", 11),
        ("atan_poly", 1),
        ("geodesic_rhs", 11),
        ("heatmap_color", 3),
        ("kerr_radius", 1),
        ("kerr_radius:let", 4),
        ("polarization_color", 3),
        ("sample_plasma.0", 12),
        ("sample_plasma.0:let", 78),
        ("sample_plasma.1", 12),
        ("sample_plasma.1:let", 78),
        ("sample_plasma.2", 12),
        ("sample_plasma.2:let", 78),
        ("sample_plasma.3", 12),
        ("sample_plasma.3:let", 78),
        ("screen_frame", 9),
        ("screen_frame:let", 21),
        ("spatial_unit", 3),
        ("spin_scale", 3),
        ("tonemap", 3),
    ];
    assert_eq!(counts, expected.map(|(n, c)| (n.to_string(), c)).to_vec());
}

proptest::proptest! {
    #[test]
    fn literal_conversion_is_exact(bits in proptest::prelude::any::<u32>()) {
        let x = f32::from_bits(bits);
        proptest::prop_assume!(x.is_finite());
        let (m, e) = f32_parts(x);
        proptest::prop_assert_eq!(m as f64 * 2f64.powi(e), x as f64);
    }

    /// Normalization only reorders: sums of the same terms in any order and
    /// grouping get one node.
    #[test]
    fn sums_are_order_independent(perm in Just((0u32..6).collect::<Vec<_>>()).prop_shuffle()) {
        let mut s = Store::default();
        let terms: Vec<Id> = (0..6).map(|i| s.input(i)).collect();
        let a = s.sum(terms.clone());
        let b = perm.iter().map(|&i| terms[i as usize]).reduce(|x, y| s.add(y, x)).unwrap();
        proptest::prop_assert_eq!(a, b);
    }
}
