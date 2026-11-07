module

public import BlackHole.WgslReassoc
public import BlackHole.WgslLets
import Mathlib.Tactic.Linarith

/-! A kernel-checkable test of `WgslReassoc.RA` between slot programs
(obligation F3).

`tests/translation.rs` records naga's own expression trees, before any
normalization, in `fixtures/naga-raw.sexp`. `NagaFixture` checks with
`chkProg` that each is an `RA`-reassociation of its model, so the domain
theorems stated for every reassociation apply to the trees naga builds.

* `std` writes the models in the form the trees use: an exact power-of-two
  scaling `GExpr.scale k a` as the product `2^k * a` naga computes (its
  exactness is the binary32 fact the model assumes), `-a < t` as `-t < a`
  (negation is exact, so both select alike), and a branch whose two sides
  are the same expression as that expression. `exact_std`: the exact value
  is unchanged.
* `chk` follows slot references on both sides, compares maximal sum and
  product chains as multisets of leaves (matched greedily), and remembers
  matched slot pairs. `chk_sound`: an accepted pair is related by `RA` after
  expanding both programs. -/

@[expose] public section

namespace BlackHole.WgslRAChk
open WgslExpr GExpr WgslLets WgslReassoc

/-! ### The models' exact rewrites -/

def std : GExpr → GExpr
  | .input i => .input i
  | .const c => .const c
  | .add a b => .add (std a) (std b)
  | .sub a b => .sub (std a) (std b)
  | .mul a b => .mul (std a) (std b)
  | .div a b => .div (std a) (std b)
  | .max a b => .max (std a) (std b)
  | .min a b => .min (std a) (std b)
  | .neg a => .neg (std a)
  | .sqrt a => .sqrt (std a)
  | .abs a => .abs (std a)
  | .invsqrt a => .invsqrt (std a)
  | .exp a => .exp (std a)
  | .exp2 a => .exp2 (std a)
  | .log a => .log (std a)
  | .log2 a => .log2 (std a)
  | .sinS a => .sinS (std a)
  | .cosS a => .cosS (std a)
  | .inh f a => .inh f (std a)
  | .tanh f a => .tanh f (std a)
  | .lt (.neg c) t a b =>
    if std a = std b then std a else .lt2 (.const (-t)) (std c) (std a) (std b)
  | .lt c t a b => if std a = std b then std a else .lt (std c) t (std a) (std b)
  | .lt2 c d a b => if std a = std b then std a else .lt2 (std c) (std d) (std a) (std b)
  | .scale k a => .mul (.const ((2:ℚ)^k)) (std a)
  | .round a => .round (std a)
  | .qsel j k a b => .qsel j (std k) (std a) (std b)

lemma std_lt {c : GExpr} (hc : ¬ ∃ c', c = .neg c') (t : ℚ) (a b : GExpr) :
    std (.lt c t a b) = if std a = std b then std a else .lt (std c) t (std a) (std b) := by
  cases c <;> simp_all [std]

theorem exact_std (v : ℕ → ℝ) : ∀ e : GExpr, exact v (std e) = exact v e
  | .input _ => rfl
  | .const _ => rfl
  | .add a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .sub a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .mul a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .div a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .max a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .min a b => by simp [std, exact, exact_std v a, exact_std v b]
  | .neg a => by simp [std, exact, exact_std v a]
  | .sqrt a => by simp [std, exact, exact_std v a]
  | .abs a => by simp [std, exact, exact_std v a]
  | .invsqrt a => by simp [std, exact, exact_std v a]
  | .exp a => by simp [std, exact, exact_std v a]
  | .exp2 a => by simp [std, exact, exact_std v a]
  | .log a => by simp [std, exact, exact_std v a]
  | .log2 a => by simp [std, exact, exact_std v a]
  | .sinS a => by simp [std, exact, exact_std v a]
  | .cosS a => by simp [std, exact, exact_std v a]
  | .inh f a => by simp [std, exact, exact_std v a]
  | .tanh f a => by simp [std, exact, exact_std v a]
  | .round a => by simp [std, exact, exact_std v a]
  | .qsel j k a b => by simp [std, exact, exact_std v k, exact_std v a, exact_std v b]
  | .scale k a => by simp [std, exact, exact_std v a]
  | .lt2 c d a b => by
    have ha := exact_std v a; have hb := exact_std v b
    have key : std a = std b → exact v a = exact v b := fun h => by rw [← ha, ← hb, h]
    simp only [std]
    split_ifs with h
    · rw [ha]; simp only [exact]; split_ifs <;> simp [key h]
    · simp [exact, exact_std v c, exact_std v d, ha, hb]
  | .lt c t a b => by
    have ha := exact_std v a; have hb := exact_std v b
    have key : std a = std b → exact v a = exact v b := fun h => by rw [← ha, ← hb, h]
    by_cases hc : ∃ c', c = .neg c'
    · obtain ⟨c, rfl⟩ := hc
      simp only [std]
      split_ifs with h
      · rw [ha]; simp only [exact]; split_ifs <;> simp [key h]
      · simp only [exact, exact_std v c, ha, hb]
        push_cast
        exact ite_congr (propext ⟨fun h => by linarith, fun h => by linarith⟩) (fun _ => rfl)
          (fun _ => rfl)
    · rw [std_lt hc]
      split_ifs with h
      · rw [ha]; simp only [exact]; split_ifs <;> simp [key h]
      · simp only [exact, exact_std v c, ha, hb]

/-! ### Slot programs -/

/-- `X` is the expansion of the slots `S`: each expanded slot is its slot
with the references expanded. `expand [] S` is one for well-formed `S`
(`fix_expand`). -/
def Fix (S X : List GExpr) : Prop :=
  X.length = S.length ∧ ∀ k (h : k < S.length), X.getD k (.input 0) = subst (lookup X) S[k]

/-- The slot that input `i` refers to, if any. -/
def refIdx (S : List GExpr) : GExpr → Option ℕ
  | .input i => if letBase ≤ i ∧ i-letBase < S.length then some (i-letBase) else none
  | _ => none

/-- Follows slot references. -/
def rs (S : List GExpr) : ℕ → GExpr → GExpr
  | f+1, .input i =>
    if h : letBase ≤ i ∧ i-letBase < S.length then rs S f S[i-letBase] else .input i
  | _, e => e

lemma lookup_ref {S X : List GExpr} (hX : Fix S X) {i : ℕ} (h : letBase ≤ i ∧ i-letBase < S.length) :
    lookup X i = subst (lookup X) S[i-letBase] := by
  rw [← hX.2 _ h.2]
  unfold lookup
  have : i-letBase < X.length := hX.1 ▸ h.2
  simp [h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]

lemma lookup_noref {S X : List GExpr} (hX : Fix S X) {i : ℕ} (h : ¬(letBase ≤ i ∧ i-letBase < S.length)) :
    lookup X i = .input i := by
  unfold lookup
  split_ifs with h1
  · have : X.length ≤ i-letBase := by rw [hX.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  · rfl

lemma subst_rs {S X : List GExpr} (hX : Fix S X) : ∀ f e, subst (lookup X) (rs S f e) = subst (lookup X) e
  | 0, e => by cases e <;> rfl
  | f+1, e => by
    cases e with
    | input i =>
      simp only [rs]
      split_ifs with h
      · rw [subst_rs hX f, subst, lookup_ref hX h]
      · rfl
    | _ => rfl

/-- A resolved node: not a reference into `S`. -/
def Resolved (S : List GExpr) (e : GExpr) : Prop := refIdx S e = none

instance (S : List GExpr) (e : GExpr) : Decidable (Resolved S e) := by
  unfold Resolved; infer_instance

lemma subst_resolved_input {S X : List GExpr} (hX : Fix S X) {i : ℕ} (h : Resolved S (.input i)) :
    subst (lookup X) (.input i) = .input i := by
  simp only [Resolved, refIdx] at h
  split_ifs at h with h1
  exact lookup_noref hX h1

/-! ### Chain leaves through references -/

def neg1 (p : Bool × GExpr) : Bool × GExpr := (!p.1, p.2)

/-- The leaves of the maximal sum chain at `e`, following references;
`none` if the fuel runs out or a leaf is an unresolved reference. A leaf
reached through a reference is returned as that reference, so the checker
can remember it. -/
def sl (S : List GExpr) : ℕ → GExpr → Option (List (Bool × GExpr))
  | 0, _ => none
  | f+1, e =>
    match rs S f e with
    | .add a b => do let la ← sl S f a; let lb ← sl S f b; pure (la ++ lb)
    | .sub a b => do let la ← sl S f a; let lb ← sl S f b; pure (la ++ lb.map neg1)
    | .neg a => do let la ← sl S f a; pure (la.map neg1)
    | e' => if Resolved S e' then some [(false, e)] else none

/-- The factors of a product of divisors, following references. -/
def ml (S : List GExpr) : ℕ → GExpr → Option (List GExpr)
  | 0, _ => none
  | f+1, e =>
    match rs S f e with
    | .mul a b => do let la ← ml S f a; let lb ← ml S f b; pure (la ++ lb)
    | e' => if Resolved S e' then some [e] else none

/-- The leaves of the maximal product chain at `e`, following references. -/
def pl (S : List GExpr) : ℕ → GExpr → Option (List (Bool × GExpr))
  | 0, _ => none
  | f+1, e =>
    match rs S f e with
    | .mul a b => do let la ← pl S f a; let lb ← pl S f b; pure (la ++ lb)
    | .div a b => do let la ← pl S f a; let lb ← ml S f b; pure (la ++ lb.map fun x => (true, x))
    | e' => if Resolved S e' then some [(false, e)] else none

def sx (X : List GExpr) (p : Bool × GExpr) : Bool × GExpr := (p.1, subst (lookup X) p.2)

lemma not_sum_subst {S X : List GExpr} (hX : Fix S X) {e : GExpr} (hs : ¬ IsSum e)
    (hr : Resolved S e) : ¬ IsSum (subst (lookup X) e) := by
  cases e with
  | input i => rw [subst_resolved_input hX hr]; simp [IsSum]
  | _ => simp_all [IsSum, subst]

lemma sumLeaves_atom {S X : List GExpr} (hX : Fix S X) {e : GExpr} (hs : ¬ IsSum e)
    (hr : Resolved S e) : sumLeaves (subst (lookup X) e) = [(false, subst (lookup X) e)] :=
  sumLeaves_of_not (not_sum_subst hX hs hr)

theorem sl_spec {S X : List GExpr} (hX : Fix S X) :
    ∀ f e L, sl S f e = some L → sumLeaves (subst (lookup X) e) = L.map (sx X)
  | 0, _, _, h => by simp [sl] at h
  | f+1, e, L, h => by
    rw [← subst_rs hX f e]
    simp only [sl] at h
    generalize hrr : rs S f e = r at h ⊢
    cases r with
    | add a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, lb, hb, rfl⟩ := h
      simp [subst, sumLeaves, sl_spec hX f a la ha, sl_spec hX f b lb hb]
    | sub a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, lb, hb, rfl⟩ := h
      simp [subst, sumLeaves, sl_spec hX f a la ha, sl_spec hX f b lb hb, neg1, sx,
        Function.comp_def]
    | neg a =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, rfl⟩ := h
      simp [subst, sumLeaves, sl_spec hX f a la ha, neg1, sx, Function.comp_def]
    | _ =>
      simp only at h
      split_ifs at h with hr
      simp only [Option.some.injEq] at h
      subst h
      rw [sumLeaves_atom hX (by simp [IsSum]) hr]
      simp only [sx, List.map_cons, List.map_nil]
      rw [← hrr, subst_rs hX f e]

lemma not_mul_subst {S X : List GExpr} (hX : Fix S X) {e : GExpr} (hs : ¬ IsMul e)
    (hr : Resolved S e) : ¬ IsMul (subst (lookup X) e) := by
  cases e with
  | input i => rw [subst_resolved_input hX hr]; simp [IsMul]
  | _ => simp_all [IsMul, subst]

lemma not_prod_subst {S X : List GExpr} (hX : Fix S X) {e : GExpr} (hs : ¬ IsProd e)
    (hr : Resolved S e) : ¬ IsProd (subst (lookup X) e) := by
  cases e with
  | input i => rw [subst_resolved_input hX hr]; simp [IsProd]
  | _ => simp_all [IsProd, subst]

theorem ml_spec {S X : List GExpr} (hX : Fix S X) :
    ∀ f e L, ml S f e = some L → mulLeaves (subst (lookup X) e) = L.map (subst (lookup X))
  | 0, _, _, h => by simp [ml] at h
  | f+1, e, L, h => by
    rw [← subst_rs hX f e]
    simp only [ml] at h
    generalize hrr : rs S f e = r at h ⊢
    cases r with
    | mul a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, lb, hb, rfl⟩ := h
      simp [subst, mulLeaves, ml_spec hX f a la ha, ml_spec hX f b lb hb]
    | _ =>
      simp only at h
      split_ifs at h with hr
      simp only [Option.some.injEq] at h
      subst h
      rw [mulLeaves_of_not (not_mul_subst hX (by simp [IsMul]) hr)]
      simp only [List.map_cons, List.map_nil]
      rw [← hrr, subst_rs hX f e]

theorem pl_spec {S X : List GExpr} (hX : Fix S X) :
    ∀ f e L, pl S f e = some L → prodLeaves (subst (lookup X) e) = L.map (sx X)
  | 0, _, _, h => by simp [pl] at h
  | f+1, e, L, h => by
    rw [← subst_rs hX f e]
    simp only [pl] at h
    generalize hrr : rs S f e = r at h ⊢
    cases r with
    | mul a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, lb, hb, rfl⟩ := h
      simp [subst, prodLeaves, pl_spec hX f a la ha, pl_spec hX f b lb hb]
    | div a b =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨la, ha, lb, hb, rfl⟩ := h
      simp [subst, prodLeaves, pl_spec hX f a la ha, ml_spec hX f b lb hb, sx, Function.comp_def]
    | _ =>
      simp only at h
      split_ifs at h with hr
      simp only [Option.some.injEq] at h
      subst h
      rw [prodLeaves_of_not (not_prod_subst hX (by simp [IsProd]) hr)]
      simp only [sx, List.map_cons, List.map_nil]
      rw [← hrr, subst_rs hX f e]

/-! ### Greedy matching of leaves -/

abbrev Memo := List (ℕ × ℕ)

/-- The first unused leaf of `L` from index `j` with sign `s` that `c`
accepts against `x`. -/
def pick (c : Memo → GExpr → GExpr → Option Memo) (memo : Memo) (s : Bool) (x : GExpr) :
    List (Bool × GExpr) → List Bool → ℕ → Option (Memo × ℕ)
  | (t, y) :: L, u :: us, j =>
    if !u && s == t then
      match c memo x y with
      | some m => some (m, j)
      | none => pick c memo s x L us (j+1)
    else pick c memo s x L us (j+1)
  | _, _, _ => none

/-- Matches every leaf of `L1` to a distinct unused leaf of `L2`. -/
def mtch (c : Memo → GExpr → GExpr → Option Memo) (L2 : List (Bool × GExpr)) :
    Memo → List (Bool × GExpr) → List Bool → Option (Memo × List ℕ)
  | memo, [], _ => some (memo, [])
  | memo, (s, x) :: L1, used =>
    match pick c memo s x L2 used 0 with
    | some (m, j) =>
      match mtch c L2 m L1 (used.set j true) with
      | some (m', js) => some (m', j :: js)
      | none => none
    | none => none

section Match
variable {c : Memo → GExpr → GExpr → Option Memo} {V : Memo → Prop} {R : GExpr → GExpr → Prop}

theorem pick_spec (hc : ∀ memo x y m, V memo → c memo x y = some m → V m ∧ R x y)
    {memo : Memo} {s : Bool} {x : GExpr} (hV : V memo) :
    ∀ (L : List (Bool × GExpr)) (us : List Bool) (j0 m j), pick c memo s x L us j0 = some (m, j) →
      V m ∧ j0 ≤ j ∧ ∃ h : j-j0 < L.length, us[j-j0]? = some false ∧ L[j-j0].1 = s ∧
        R x L[j-j0].2
  | [], _, _, _, _, h => by simp [pick] at h
  | (_ :: _), [], _, _, _, h => by simp [pick] at h
  | (t, y) :: L, u :: us, j0, m, j, h => by
    simp only [pick] at h
    split_ifs at h with hu
    · split at h
      · rename_i m' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := hc _ _ _ _ hV hm
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hu
        refine ⟨h1, le_rfl, by simp, ?_⟩
        simp [hu.1, hu.2, h2]
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pick_spec hc hV L us (j0+1) m j h
        refine ⟨h1, by omega, by simp only [List.length_cons]; omega, ?_⟩
        have e : j-j0 = (j-(j0+1))+1 := by omega
        simp only [e, List.getElem?_cons_succ, List.getElem_cons_succ]
        exact ⟨h4, h5, h6⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pick_spec hc hV L us (j0+1) m j h
      refine ⟨h1, by omega, by simp only [List.length_cons]; omega, ?_⟩
      have e : j-j0 = (j-(j0+1))+1 := by omega
      simp only [e, List.getElem?_cons_succ, List.getElem_cons_succ]
      exact ⟨h4, h5, h6⟩

theorem mtch_spec (hc : ∀ memo x y m, V memo → c memo x y = some m → V m ∧ R x y)
    (L2 : List (Bool × GExpr)) :
    ∀ (memo : Memo) (L1 : List (Bool × GExpr)) (used : List Bool) m js, V memo →
      mtch c L2 memo L1 used = some (m, js) →
      V m ∧ js.length = L1.length ∧ js.Nodup ∧
        ∀ k (hk : k < js.length) (hk1 : k < L1.length), ∃ h : js[k] < L2.length,
          used[js[k]]? = some false ∧ L2[js[k]].1 = L1[k].1 ∧ R L1[k].2 L2[js[k]].2
  | memo, [], used, m, js, hV, h => by
    simp only [mtch, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hV]
  | memo, (s, x) :: L1, used, m, js, hV, h => by
    simp only [mtch] at h
    split at h
    · rename_i m1 j hp
      split at h
      · rename_i m2 js' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv1, -, hj, hu, hs, hr⟩ := pick_spec hc hV L2 used 0 m1 j hp
        simp only [Nat.sub_zero] at hj hu hs hr
        obtain ⟨hv2, hl, hnd, hall⟩ := mtch_spec hc L2 m1 L1 (used.set j true) m2 js' hv1 hm
        have hjl : j < used.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hu; simp at hu
        have hset : (used.set j true)[j]? = some true := by simp [hjl]
        refine ⟨hv2, by simp [hl], ?_, ?_⟩
        · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
          obtain ⟨k, hk, he⟩ := List.getElem_of_mem hmem
          obtain ⟨_, hu', -⟩ := hall k hk (by omega)
          rw [he, hset] at hu'
          simp at hu'
        · intro k hk hk1
          cases k with
          | zero => exact ⟨hj, hu, hs, hr⟩
          | succ k =>
            have hk' : k < js'.length := by simpa using hk
            obtain ⟨h1, h2, h3, h4⟩ := hall k hk' (by simpa using hk1)
            refine ⟨h1, ?_, h3, h4⟩
            have hne : j ≠ js'[k] := by
              intro he; rw [← he, hset] at h2; simp at h2
            rwa [List.getElem?_set_ne hne] at h2
      · simp at h
    · simp at h

end Match

/-- A list of distinct indices below `n`, of length `n`, is a permutation. -/
lemma perm_of_list {n : ℕ} (js : List ℕ) (hl : js.length = n) (hnd : js.Nodup)
    (hb : ∀ k (hk : k < js.length), js[k] < n) :
    ∃ σ : Fin n ≃ Fin n, ∀ i, (σ i : ℕ) = js[(i : ℕ)]'(by omega) := by
  let f : Fin n → Fin n := fun i => ⟨js[(i : ℕ)]'(by omega), hb _ _⟩
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f, Fin.mk.injEq] at hab
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp hab)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun i => rfl⟩

lemma ra_sum_of {e e' : GExpr} (he : IsSum e) (he' : IsSum e') {L1 L2 : List (Bool × GExpr)}
    (h1 : sumLeaves e = L1) (h2 : sumLeaves e' = L2) (σ : Fin L1.length ≃ Fin L2.length)
    (hs : ∀ i, (L2[σ i]).1 = (L1[i]).1) (hl : ∀ i, RA (L1[i]).2 (L2[σ i]).2) : RA e e' := by
  subst h1 h2; exact RA.sum he he' σ hs hl

lemma ra_prod_of {e e' : GExpr} (he : IsProd e) (he' : IsProd e') {L1 L2 : List (Bool × GExpr)}
    (h1 : prodLeaves e = L1) (h2 : prodLeaves e' = L2) (σ : Fin L1.length ≃ Fin L2.length)
    (hs : ∀ i, (L2[σ i]).1 = (L1[i]).1) (hl : ∀ i, RA (L1[i]).2 (L2[σ i]).2) : RA e e' := by
  subst h1 h2; exact RA.prod he he' σ hs hl

/-- Leaves matched by `mtch` give the permutation `RA.sum`/`RA.prod` needs. -/
lemma chain_ra {XM XN : List GExpr} {L1 L2 : List (Bool × GExpr)} {js : List ℕ}
    (hlen : L1.length = L2.length) (hl : js.length = L1.length) (hnd : js.Nodup)
    (hall : ∀ k (hk : k < js.length) (hk1 : k < L1.length), ∃ h : js[k] < L2.length,
      L2[js[k]].1 = L1[k].1 ∧ RA (subst (lookup XM) L1[k].2) (subst (lookup XN) L2[js[k]].2)) :
    ∃ σ : Fin (L1.map (sx XM)).length ≃ Fin (L2.map (sx XN)).length,
      (∀ i, ((L2.map (sx XN))[σ i]).1 = ((L1.map (sx XM))[i]).1) ∧
      (∀ i, RA ((L1.map (sx XM))[i]).2 ((L2.map (sx XN))[σ i]).2) := by
  obtain ⟨σ, hσ⟩ := perm_of_list (n := L1.length) js hl hnd
    (fun k hk => by obtain ⟨h, -⟩ := hall k hk (by omega); omega)
  refine ⟨(finCongr (by simp)).trans (σ.trans (finCongr (by simp [hlen]))), ?_, ?_⟩
  · intro i
    have hi : (i : ℕ) < L1.length := by have := i.2; simpa using this
    obtain ⟨h, h1, -⟩ := hall i (by omega) hi
    simp [sx, hσ, h1]
  · intro i
    have hi : (i : ℕ) < L1.length := by have := i.2; simpa using this
    obtain ⟨h, -, h2⟩ := hall i (by omega) hi
    simp [sx, hσ, h2]

/-! ### The checker -/

/-- One pair of resolved nodes, with `c` checking the children. -/
def chkNode (M N : List GExpr) (c : Memo → GExpr → GExpr → Option Memo) (f : ℕ) (memo : Memo)
    (a b : GExpr) : Option Memo :=
  if Resolved M a ∧ Resolved N b then
    if IsSum a ∨ IsSum b then
      if IsSum a ∧ IsSum b then
        match sl M f a, sl N f b with
        | some L1, some L2 =>
          if L1.length = L2.length then
            (mtch c L2 memo L1 (List.replicate L2.length false)).map Prod.fst
          else none
        | _, _ => none
      else none
    else if IsProd a ∨ IsProd b then
      if IsProd a ∧ IsProd b then
        match pl M f a, pl N f b with
        | some L1, some L2 =>
          if L1.length = L2.length then
            (mtch c L2 memo L1 (List.replicate L2.length false)).map Prod.fst
          else none
        | _, _ => none
      else none
    else
      match a, b with
      | .input i, .input j => if i = j then some memo else none
      | .const p, .const q => if p = q then some memo else none
      | .sqrt x, .sqrt y => c memo x y
      | .abs x, .abs y => c memo x y
      | .invsqrt x, .invsqrt y => c memo x y
      | .exp x, .exp y => c memo x y
      | .exp2 x, .exp2 y => c memo x y
      | .log x, .log y => c memo x y
      | .log2 x, .log2 y => c memo x y
      | .sinS x, .sinS y => c memo x y
      | .cosS x, .cosS y => c memo x y
      | .round x, .round y => c memo x y
      | .max x1 x2, .max y1 y2 => (c memo x1 y1).bind fun m => c m x2 y2
      | .min x1 x2, .min y1 y2 => (c memo x1 y1).bind fun m => c m x2 y2
      | .inh g x, .inh g' y => if g = g' then c memo x y else none
      | .tanh g x, .tanh g' y => if g = g' then c memo x y else none
      | .scale k x, .scale k' y => if k = k' then c memo x y else none
      | .lt p t x y, .lt p' t' x' y' =>
        if t = t' then ((c memo p p').bind fun m => c m x x').bind fun m => c m y y' else none
      | .lt2 p q x y, .lt2 p' q' x' y' =>
        (((c memo p p').bind fun m => c m q q').bind fun m => c m x x').bind fun m => c m y y'
      | .qsel j k x y, .qsel j' k' x' y' =>
        if j = j' then ((c memo k k').bind fun m => c m x x').bind fun m => c m y y' else none
      | _, _ => none
  else none

/-- `e1` (model, slots `M`) against `e2` (naga, slots `N`); matched slot
pairs are remembered. -/
def chk (M N : List GExpr) : ℕ → Memo → GExpr → GExpr → Option Memo
  | 0, _, _, _ => none
  | f+1, memo, e1, e2 =>
    match refIdx M e1, refIdx N e2 with
    | some k1, some k2 =>
      if (k1, k2) ∈ memo then some memo
      else (chkNode M N (chk M N f) f memo (rs M f e1) (rs N f e2)).map ((k1, k2) :: ·)
    | _, _ => chkNode M N (chk M N f) f memo (rs M f e1) (rs N f e2)

/-- Memo pairs are slot pairs whose expansions are related. -/
def MemoOK (XM XN : List GExpr) (memo : Memo) : Prop :=
  ∀ p ∈ memo, RA (subst (lookup XM) (.input (letBase+p.1))) (subst (lookup XN) (.input (letBase+p.2)))

lemma isSum_subst (σ : ℕ → GExpr) {a : GExpr} (h : IsSum a) : IsSum (subst σ a) := by
  cases a <;> simp_all [IsSum, subst]

lemma isProd_subst (σ : ℕ → GExpr) {a : GExpr} (h : IsProd a) : IsProd (subst σ a) := by
  cases a <;> simp_all [IsProd, subst]

lemma bind_some {α β : Type} {o : Option α} {g : α → Option β} {b : β}
    (h : o.bind g = some b) : ∃ a, o = some a ∧ g a = some b := by
  cases o <;> simp_all

theorem chkNode_sound {M N XM XN : List GExpr} (hM : Fix M XM) (hN : Fix N XN)
    {c : Memo → GExpr → GExpr → Option Memo}
    (hc : ∀ memo x y m, MemoOK XM XN memo → c memo x y = some m →
      MemoOK XM XN m ∧ RA (subst (lookup XM) x) (subst (lookup XN) y))
    {f : ℕ} {memo m : Memo} {a b : GExpr} (hV : MemoOK XM XN memo)
    (h : chkNode M N c f memo a b = some m) :
    MemoOK XM XN m ∧ RA (subst (lookup XM) a) (subst (lookup XN) b) := by
  unfold chkNode at h
  split_ifs at h with hr hs hs2 hp hp2
  · -- sum chains
    split at h
    · rename_i L1 L2 h1 h2
      split_ifs at h with hlen
      obtain ⟨⟨m', js⟩, hmt, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hm, hl, hnd, hall⟩ := mtch_spec (R := fun x y => RA (subst (lookup XM) x)
        (subst (lookup XN) y)) hc L2 memo L1 _ m' js hV hmt
      refine ⟨hm, ?_⟩
      obtain ⟨σ, hσs, hσl⟩ := chain_ra (XM := XM) (XN := XN) hlen hl hnd
        (fun k hk hk1 => by obtain ⟨h, -, h3, h4⟩ := hall k hk hk1; exact ⟨h, h3, h4⟩)
      exact ra_sum_of (isSum_subst _ hs2.1) (isSum_subst _ hs2.2) (sl_spec hM _ _ _ h1)
        (sl_spec hN _ _ _ h2) σ hσs hσl
    · simp at h
  · -- product chains
    split at h
    · rename_i L1 L2 h1 h2
      split_ifs at h with hlen
      obtain ⟨⟨m', js⟩, hmt, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hm, hl, hnd, hall⟩ := mtch_spec (R := fun x y => RA (subst (lookup XM) x)
        (subst (lookup XN) y)) hc L2 memo L1 _ m' js hV hmt
      refine ⟨hm, ?_⟩
      obtain ⟨σ, hσs, hσl⟩ := chain_ra (XM := XM) (XN := XN) hlen hl hnd
        (fun k hk hk1 => by obtain ⟨h, -, h3, h4⟩ := hall k hk hk1; exact ⟨h, h3, h4⟩)
      exact ra_prod_of (isProd_subst _ hp2.1) (isProd_subst _ hp2.2) (pl_spec hM _ _ _ h1)
        (pl_spec hN _ _ _ h2) σ hσs hσl
    · simp at h
  · -- congruences
    obtain ⟨hra, hrb⟩ := hr
    split at h <;> (try simp only [reduceCtorEq] at h)
    all_goals first
      | (split_ifs at h with he; subst he; simp only [Option.some.injEq] at h; subst h
         first
           | exact ⟨hV, by rw [subst_resolved_input hM hra, subst_resolved_input hN hrb]; exact RA.input _⟩
           | exact ⟨hV, by simp only [subst]; exact RA.const _⟩)
      | (obtain ⟨h1, h2⟩ := hc _ _ _ _ hV h
         first
           | exact ⟨h1, by simp only [subst]; exact RA.sqrt h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.abs h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.invsqrt h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.exp h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.exp2 h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.log h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.log2 h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.sinS h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.cosS h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.round h2⟩)
      | (obtain ⟨m1, hm1, hm2⟩ := bind_some h
         obtain ⟨v1, r1⟩ := hc _ _ _ _ hV hm1
         obtain ⟨v2, r2⟩ := hc _ _ _ _ v1 hm2
         first
           | exact ⟨v2, by simp only [subst]; exact RA.max r1 r2⟩
           | exact ⟨v2, by simp only [subst]; exact RA.min r1 r2⟩)
      | (split_ifs at h with he
         subst he
         obtain ⟨h1, h2⟩ := hc _ _ _ _ hV h
         first
           | exact ⟨h1, by simp only [subst]; exact RA.inh _ h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.tanh _ h2⟩
           | exact ⟨h1, by simp only [subst]; exact RA.scale _ h2⟩)
      | (split_ifs at h with he
         subst he
         obtain ⟨m2, hm2, hm3⟩ := bind_some h
         obtain ⟨m1, hm1, hm2⟩ := bind_some hm2
         obtain ⟨v1, r1⟩ := hc _ _ _ _ hV hm1
         obtain ⟨v2, r2⟩ := hc _ _ _ _ v1 hm2
         obtain ⟨v3, r3⟩ := hc _ _ _ _ v2 hm3
         first
           | exact ⟨v3, by simp only [subst]; exact RA.lt _ r1 r2 r3⟩
           | exact ⟨v3, by simp only [subst]; exact RA.qsel _ r1 r2 r3⟩)
      | (obtain ⟨m3, hm3, hm4⟩ := bind_some h
         obtain ⟨m2, hm2, hm3⟩ := bind_some hm3
         obtain ⟨m1, hm1, hm2⟩ := bind_some hm2
         obtain ⟨v1, r1⟩ := hc _ _ _ _ hV hm1
         obtain ⟨v2, r2⟩ := hc _ _ _ _ v1 hm2
         obtain ⟨v3, r3⟩ := hc _ _ _ _ v2 hm3
         obtain ⟨v4, r4⟩ := hc _ _ _ _ v3 hm4
         exact ⟨v4, by simp only [subst]; exact RA.lt2 r1 r2 r3 r4⟩)

lemma refIdx_eq {S : List GExpr} {e : GExpr} {k : ℕ} (h : refIdx S e = some k) :
    e = .input (letBase+k) := by
  cases e <;> simp only [refIdx, reduceCtorEq] at h
  split_ifs at h with h1
  simp only [Option.some.injEq] at h
  subst h
  rw [Nat.add_sub_cancel' h1.1]

theorem chk_sound {M N XM XN : List GExpr} (hM : Fix M XM) (hN : Fix N XN) :
    ∀ f memo e1 e2 m, MemoOK XM XN memo → chk M N f memo e1 e2 = some m →
      MemoOK XM XN m ∧ RA (subst (lookup XM) e1) (subst (lookup XN) e2)
  | 0, _, _, _, _, _, h => by simp [chk] at h
  | f+1, memo, e1, e2, m, hV, h => by
    have ih := chk_sound hM hN f
    simp only [chk] at h
    rw [← subst_rs hM f e1, ← subst_rs hN f e2]
    split at h
    · rename_i k1 k2 h1 h2
      have e1e := refIdx_eq h1
      have e2e := refIdx_eq h2
      split_ifs at h with hmem
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨hV, ?_⟩
        rw [subst_rs hM f e1, subst_rs hN f e2, e1e, e2e]
        exact hV _ hmem
      · obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hv, hra⟩ := chkNode_sound hM hN ih hV hm'
        refine ⟨?_, hra⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · rw [← e1e, ← e2e, ← subst_rs hM f e1, ← subst_rs hN f e2]; exact hra
        · exact hv p hp
    · exact chkNode_sound hM hN ih hV h

/-- Checks the outputs pairwise, carrying the memo along. -/
def chkOuts (M N : List GExpr) (f : ℕ) : Memo → List GExpr → List GExpr → Bool
  | _, [], [] => true
  | memo, e1 :: o1, e2 :: o2 =>
    match chk M N f memo e1 e2 with
    | some m => chkOuts M N f m o1 o2
    | none => false
  | _, _, _ => false

theorem chkOuts_sound {M N XM XN : List GExpr} (hM : Fix M XM) (hN : Fix N XN) (f : ℕ) :
    ∀ memo o1 o2, MemoOK XM XN memo → chkOuts M N f memo o1 o2 = true →
      o1.length = o2.length ∧ ∀ i (h1 : i < o1.length) (h2 : i < o2.length),
        RA (subst (lookup XM) o1[i]) (subst (lookup XN) o2[i])
  | _, [], [], _, _ => by simp
  | memo, e1 :: o1, e2 :: o2, hV, h => by
    simp only [chkOuts] at h
    split at h
    · rename_i m hm
      obtain ⟨hv, hra⟩ := chk_sound hM hN f memo e1 e2 m hV hm
      obtain ⟨hl, hall⟩ := chkOuts_sound hM hN f m o1 o2 hv h
      refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
      cases i with
      | zero => exact hra
      | succ i => exact hall i (by simpa using h1) (by simpa using h2)
    · simp at h
  | _, [], _ :: _, _, h => by simp [chkOuts] at h
  | _, _ :: _, [], _, h => by simp [chkOuts] at h

/-! ### Well-formed slot programs -/

/-- Every input of `e` is a kernel input or one of the first `n` slots
(`inh`/`tanh` programs read their own argument and are skipped). -/
def refsLt (n : ℕ) : GExpr → Bool
  | .input i => decide (i < letBase ∨ i-letBase < n)
  | .const _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .max a b | .min a b => refsLt n a && refsLt n b
  | .neg a | .sqrt a | .abs a | .invsqrt a | .exp a | .exp2 a | .log a | .log2 a | .sinS a
  | .cosS a | .round a | .inh _ a | .tanh _ a | .scale _ a => refsLt n a
  | .lt c _ a b => refsLt n c && refsLt n a && refsLt n b
  | .lt2 c d a b => refsLt n c && refsLt n d && refsLt n a && refsLt n b
  | .qsel _ k a b => refsLt n k && refsLt n a && refsLt n b

/-- Each slot reads only earlier slots. -/
def WF (S : List GExpr) : Bool :=
  (List.range S.length).all fun k => refsLt k (S.getD k (.const 0))

lemma subst_congr_lt {σ τ : ℕ → GExpr} {n : ℕ} (hστ : ∀ i, (i < letBase ∨ i-letBase < n) → σ i = τ i) :
    ∀ e, refsLt n e = true → subst σ e = subst τ e
  | .input i, h => by simp only [refsLt, decide_eq_true_eq] at h; exact hστ i h
  | .const _, _ => rfl
  | .add a b, h | .sub a b, h | .mul a b, h | .div a b, h | .max a b, h | .min a b, h => by
    simp only [refsLt, Bool.and_eq_true] at h
    simp [subst, subst_congr_lt hστ a h.1, subst_congr_lt hστ b h.2]
  | .neg a, h | .sqrt a, h | .abs a, h | .invsqrt a, h | .exp a, h | .exp2 a, h | .log a, h
  | .log2 a, h | .sinS a, h | .cosS a, h | .round a, h | .inh _ a, h | .tanh _ a, h
  | .scale _ a, h => by
    simp only [refsLt] at h
    simp [subst, subst_congr_lt hστ a h]
  | .lt c _ a b, h => by
    simp only [refsLt, Bool.and_eq_true] at h
    simp [subst, subst_congr_lt hστ c h.1.1, subst_congr_lt hστ a h.1.2, subst_congr_lt hστ b h.2]
  | .lt2 c d a b, h => by
    simp only [refsLt, Bool.and_eq_true] at h
    simp [subst, subst_congr_lt hστ c h.1.1.1, subst_congr_lt hστ d h.1.1.2,
      subst_congr_lt hστ a h.1.2, subst_congr_lt hστ b h.2]
  | .qsel _ k a b, h => by
    simp only [refsLt, Bool.and_eq_true] at h
    simp [subst, subst_congr_lt hστ k h.1.1, subst_congr_lt hστ a h.1.2, subst_congr_lt hστ b h.2]

lemma expand_spec : ∀ (S done : List GExpr),
    (expand done S).length = done.length+S.length ∧
    (expand done S).take done.length = done ∧
    ∀ k (hk : k < S.length), (expand done S).getD (done.length+k) (.input 0) =
      subst (lookup ((expand done S).take (done.length+k))) S[k]
  | [], done => by simp [expand]
  | e :: S, done => by
    obtain ⟨h1, h2, h3⟩ := expand_spec S (done ++ [subst (lookup done) e])
    simp only [expand, List.length_append, List.length_singleton] at h1 h2 h3 ⊢
    have hd : (expand (done ++ [subst (lookup done) e]) S).take done.length = done := by
      have := congrArg (List.take done.length) h2
      rwa [List.take_take, min_eq_left (by omega), List.take_left'] at this
    refine ⟨by simp [h1]; omega, hd, fun k hk => ?_⟩
    cases k with
    | zero =>
      have hlt : done.length < (expand (done ++ [subst (lookup done) e]) S).length := by omega
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, hd]
      have := congrArg (fun l => l[done.length]?) h2
      simp only [List.getElem?_take_of_lt (by omega : done.length < done.length+1),
        List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_singleton,
        List.getElem?_eq_getElem hlt] at this
      simpa using this
    | succ k =>
      have := h3 k (by simpa using hk)
      rw [show done.length+(k+1) = done.length+1+k by omega]
      simpa using this

theorem fix_expand (S : List GExpr) (hwf : WF S = true) : Fix S (expand [] S) := by
  obtain ⟨h1, -, h3⟩ := expand_spec S []
  simp only [List.length_nil, Nat.zero_add] at h1 h3
  refine ⟨h1, fun k hk => ?_⟩
  rw [h3 k hk]
  have hk' : refsLt k S[k] = true := by
    have := List.all_eq_true.mp hwf k (List.mem_range.mpr hk)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
  apply subst_congr_lt _ _ hk'
  intro i hi
  unfold lookup
  split_ifs with hl
  · have hi' : i-letBase < k := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp [hi']
  · rfl

/-- `chkProg` accepts: every output of the naga program `N` is a reassociation
of the matching output of the model `M`. -/
def chkProg (M N : List GExpr) (om on : List GExpr) : Bool :=
  WF M && WF N && chkOuts M N 100000 [] om on

theorem chkProg_sound {M N om on : List GExpr} (h : chkProg M N om on = true) :
    om.length = on.length ∧ ∀ i (h1 : i < om.length) (h2 : i < on.length),
      RA (withLets M om[i]) (withLets N on[i]) := by
  simp only [chkProg, Bool.and_eq_true] at h
  obtain ⟨⟨hM, hN⟩, h⟩ := h
  exact chkOuts_sound (fix_expand M hM) (fix_expand N hN) _ [] om on (by simp [MemoOK]) h

end BlackHole.WgslRAChk
