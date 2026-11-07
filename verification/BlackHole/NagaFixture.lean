module

public import BlackHole.KernelFixture
public import BlackHole.WgslRAChk

/-! naga's own expression trees are reassociations of the models
(obligation F3).

`fixtures/naga-raw.sexp` records, for every kernel `tests/translation.rs`
compares, the trees naga's WGSL front end builds, before any normalization,
as slot programs. The test's symbolic evaluator reads naga's IR into these
trees with the documented exact rewrites for branches (`a <= b` as
`!(b < a)`, `-a < c` as `-c < a`, `s == 0` as `!(-s < 0)` for nonnegative
`s`, the quadrant selection as `qsel`), inlines calls other than `sincos`,
and unrolls loops; that evaluator and the fixture writer remain trusted.

`check F m n` runs `WgslRAChk.chkProg` on model `m` (after `std`) and naga's
program `n`; `check_sound` turns an accepted check into `RA` between every
expanded output. The kernel checks every compared kernel, for the trees of
naga's WGSL front end and for those read back from the SPIR-V naga writes
(`naga-raw-spirv.sexp`): `naga_small` here, `add_kerr` in `NagaFixtureKerr`
and `NagaFixtureKerrSpirv`, and `sample_plasma` in `NagaFixturePlasma`.
So each domain theorem stated for every reassociation of a model holds for
the tree naga builds, read with `std`'s rewrites (`exact_withLets_std`: they
do not change the exact value). -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr GExpr WgslLets WgslRAChk KernelFixture

/-- A polynomial program as a `GExpr`; `divc a c` is the division by `c`. -/
def toG : WgslPoly.PExpr → GExpr
  | .input i => .input i
  | .const c => .const c
  | .add a b => .add (toG a) (toG b)
  | .sub a b => .sub (toG a) (toG b)
  | .mul a b => .mul (toG a) (toG b)
  | .neg a => .neg (toG a)
  | .divc a c => .div (toG a) (.const c)

/-- The rows named `n`. -/
def rowsOf (F : List (String × GExpr)) (n : String) : List GExpr :=
  (F.filter fun p => p.1 == n).map (·.2)

/-- The models of both fixtures, which `KernelFixture.fixture_eq` and
`branching_fixture_eq` prove equal to the Lean definitions. -/
def models : List (String × GExpr) := (fixture.map fun p => (p.1, toG p.2)) ++ branchingFixture

def modelSlots (m : String) : List GExpr := (rowsOf models (m ++ ":let")).map std
def modelOuts (m : String) (σ : ℕ → GExpr) : List GExpr :=
  (rowsOf models m).map fun e => std (subst σ e)
def nagaSlots (F : List (String × GExpr)) (n : String) : List GExpr := rowsOf F (n ++ ":let")
def nagaOuts (F : List (String × GExpr)) (n : String) : List GExpr := rowsOf F n

/-- Model `m`, with inputs renamed by `σ`, against naga's program `n` in the
fixture `F` (`nagaFixture` for the WGSL front end, `nagaSpirvFixture` for
the SPIR-V round trip). -/
def check (F : List (String × GExpr)) (m n : String) (σ : ℕ → GExpr := .input) : Bool :=
  chkProg (modelSlots m) (nagaSlots F n) (modelOuts m σ) (nagaOuts F n)

theorem check_sound {F : List (String × GExpr)} {m n : String} {σ : ℕ → GExpr}
    (h : check F m n σ = true) :
    (modelOuts m σ).length = (nagaOuts F n).length ∧ ∀ i (h1 : i < (modelOuts m σ).length)
      (h2 : i < (nagaOuts F n).length),
      WgslReassoc.RA (withLets (modelSlots m) (modelOuts m σ)[i])
        (withLets (nagaSlots F n) (nagaOuts F n)[i]) :=
  chkProg_sound h

/-! #### `std` keeps the exact value of a slot program -/

lemma exact_subst (v : ℕ → ℝ) (σ : ℕ → GExpr) :
    ∀ e, exact v (subst σ e) = exact (fun i => exact v (σ i)) e
  | .input _ => rfl
  | .const _ => rfl
  | .add a b | .sub a b | .mul a b | .div a b | .max a b | .min a b => by
    simp [subst, exact, exact_subst v σ a, exact_subst v σ b]
  | .neg a | .sqrt a | .abs a | .invsqrt a | .exp a | .exp2 a | .log a | .log2 a | .sinS a
  | .cosS a | .round a | .tanh _ a | .scale _ a => by
    simp [subst, exact, exact_subst v σ a]
  | .inh f a => by simp [subst, exact, exact_subst v σ a]
  | .lt c t a b => by simp [subst, exact, exact_subst v σ c, exact_subst v σ a, exact_subst v σ b]
  | .lt2 c d a b => by
    simp [subst, exact, exact_subst v σ c, exact_subst v σ d, exact_subst v σ a, exact_subst v σ b]
  | .qsel j k a b => by
    simp [subst, exact, exact_subst v σ k, exact_subst v σ a, exact_subst v σ b]

lemma lookup_append (done : List GExpr) (x : GExpr) (i : ℕ) :
    lookup (done ++ [x]) i =
      if letBase ≤ i ∧ i-letBase = done.length then x else lookup done i := by
  unfold lookup
  by_cases h1 : letBase ≤ i
  · by_cases h2 : i-letBase = done.length
    · simp only [h1, h2, and_self, ↓reduceIte]
      simp [List.getD_eq_getElem?_getD]
    · simp only [h1, h2, and_false, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rcases Nat.lt_or_gt_of_ne h2 with h | h
      · rw [List.getElem?_append_left h]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  · simp only [h1, false_and, ↓reduceIte]

lemma exact_expand_std (v : ℕ → ℝ) : ∀ (S done done' : List GExpr),
    done.length = done'.length → (∀ i, exact v (lookup done i) = exact v (lookup done' i)) →
    (expand done S).length = (expand done' (S.map std)).length ∧
      ∀ i, exact v (lookup (expand done S) i) = exact v (lookup (expand done' (S.map std)) i)
  | [], _, _, hl, he => ⟨hl, he⟩
  | e :: S, done, done', hl, he => by
    simp only [expand, List.map_cons]
    apply exact_expand_std v S
    · simp [hl]
    · intro i
      rw [lookup_append, lookup_append, ← hl]
      split_ifs
      · rw [exact_subst, exact_subst, exact_std]
        exact congrArg (fun w => exact w e) (funext he)
      · exact he i

/-- `std` keeps the exact value of every output of a slot program. -/
theorem exact_withLets_std (v : ℕ → ℝ) (S : List GExpr) (e : GExpr) :
    exact v (withLets (S.map std) (std e)) = exact v (withLets S e) := by
  obtain ⟨-, he⟩ := exact_expand_std v S [] [] rfl (fun _ => rfl)
  rw [withLets, withLets, exact_subst, exact_subst, exact_std]
  exact congrArg (fun w => exact w e) (funext fun i => (he i).symm)

/-! #### The checks -/

/-- Every compared kernel except `add_kerr` and `sample_plasma`. -/
def small : List String :=
  ["geodesic_rhs", "atan_poly", "tonemap", "heatmap_color", "polarization_color", "spatial_unit",
    "screen_frame", "atan2_arith", "kerr_radius", "sincos", "transfer_phi", "faraday_rotation",
    "polarized_cell"]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small : small.all (fun n => check nagaFixture n n) = true := by decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv : small.all (fun n => check nagaSpirvFixture n n) = true := by
  decide +kernel

end BlackHole.NagaFixture
