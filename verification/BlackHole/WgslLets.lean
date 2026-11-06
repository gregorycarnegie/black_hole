module

public import BlackHole.WgslExpr

/-! Kernel models written with `let` slots (obligations F2, F3).

A large WGSL kernel reuses its `let` values many times, so its expression
tree, in which every use is a separate copy, can have millions of nodes. Such
a model is written as a list of slots: slot `k` is an expression that reads
the kernel inputs and, through inputs `letBase + j`, earlier slots `j < k`.
`expand` substitutes every slot into the later ones, and `withLets` gives an
output expression over the kernel inputs alone.

The model is the expanded tree, so `GExpr.error` and every bound about it are
unchanged: each copy of a shared value may still round independently. The
slots only make the model small enough to print and compare with the naga IR
(`KernelFixture`, `tests/translation.rs`). -/

@[expose] public section

namespace BlackHole.WgslLets
open WgslExpr GExpr

/-- Inputs from here on refer to `let` slots. -/
def letBase : ℕ := 1000000

/-- The value of slot `k`, as an input of later slots. -/
def ref (k : ℕ) : GExpr := input (letBase+k)

/-- Replaces each input `i` by `σ i`. The programs inside `inh` and `tanh`
read their own argument as input 0 and are left unchanged. -/
def subst (σ : ℕ → GExpr) : GExpr → GExpr
  | .input i => σ i
  | .const c => const c
  | .add a b => add (subst σ a) (subst σ b)
  | .sub a b => sub (subst σ a) (subst σ b)
  | .mul a b => mul (subst σ a) (subst σ b)
  | .div a b => div (subst σ a) (subst σ b)
  | .max a b => max (subst σ a) (subst σ b)
  | .min a b => min (subst σ a) (subst σ b)
  | .neg a => neg (subst σ a)
  | .sqrt a => sqrt (subst σ a)
  | .abs a => abs (subst σ a)
  | .invsqrt a => invsqrt (subst σ a)
  | .exp a => exp (subst σ a)
  | .exp2 a => exp2 (subst σ a)
  | .log a => log (subst σ a)
  | .log2 a => log2 (subst σ a)
  | .sinS a => sinS (subst σ a)
  | .cosS a => cosS (subst σ a)
  | .inh f a => inh f (subst σ a)
  | .tanh f a => tanh f (subst σ a)
  | .lt c t a b => lt (subst σ c) t (subst σ a) (subst σ b)
  | .lt2 a b x y => lt2 (subst σ a) (subst σ b) (subst σ x) (subst σ y)

/-- Inputs below `letBase` stay; slot references read the expanded slots. -/
def lookup (slots : List GExpr) (i : ℕ) : GExpr :=
  if letBase ≤ i then slots.getD (i-letBase) (input i) else input i

/-- Every slot expanded over the kernel inputs, in order. -/
def expand : List GExpr → List GExpr → List GExpr
  | done, [] => done
  | done, e :: es => expand (done ++ [subst (lookup done) e]) es

/-- An output of a slot program, over the kernel inputs. -/
def withLets (slots : List GExpr) (e : GExpr) : GExpr := subst (lookup (expand [] slots)) e

/-- Kernel inputs extended by computed slot values. -/
def env (w : ℕ → ℝ) (vals : List ℝ) (i : ℕ) : ℝ :=
  if letBase ≤ i then vals.getD (i-letBase) (w i) else w i

/-- A WGSL evaluation in which each `let` slot is computed once, as the naga
IR computes it, and later slots read that value. This is narrower than the
tree semantics of `withLets`, where each copy may round independently. -/
def SlotsComputes (w : ℕ → ℝ) : List GExpr → List ℝ → List ℝ → Prop
  | [], done, vals => vals = done
  | e :: es, done, vals => ∃ y, Computes (env w done) e y ∧ SlotsComputes w es (done ++ [y]) vals

end BlackHole.WgslLets
