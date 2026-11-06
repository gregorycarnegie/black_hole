module

public import BlackHole.WgslReassoc

/-! Error bounds for every role-preserving association of a product chain
(obligation F2).

`mul_group` bounds every association of a product of divisors by its
factors' relative errors, and `prod_bound` every association of a chain of
`*` and `/` that keeps each factor in its role (`WgslReassoc.prodLeaves`):
numerators enter through `|t|+B`, divisors through the margin
`2 - Π(1+B/|t|)(1+U')ᵐ⁻¹`, and every division in the chain is `Safe`. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslReassoc
open Wgsl WgslPoly WgslExpr GExpr

/-! The per-operation relative error of a product, with the flush-to-zero
allowance absorbed for products of magnitude at least `2⁻¹⁰⁰`. -/
def U' : ℝ := WgslPoly.U+1/2^26

lemma U'_pos : 0 < U' := by unfold U'; have := WgslPoly.U_pos; positivity

lemma η_absorb {x : ℝ} (hx : 1/2^100 ≤ x) : η ≤ (U'-WgslPoly.U)*x := by
  unfold U'; have : η = 1/2^126 := rfl
  rw [this]; ring_nf; nlinarith

lemma prod_one_le (L : List GExpr) (f : GExpr → ℝ) (hf : ∀ x ∈ L, 0 ≤ f x) :
    1 ≤ (L.map fun x => 1+f x).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 := hf x (by simp); have h2 := ih fun y hy => hf y (by simp [hy])
    nlinarith

lemma abs_prod_map (L : List GExpr) (v : ℕ → ℝ) :
    |(L.map fun x => x.exact v).prod| = (L.map fun x => |x.exact v|).prod := by
  induction L with
  | nil => simp
  | cons x L ih => simp [abs_mul, ih]

lemma prod_min_le (L : List GExpr) (v : ℕ → ℝ) :
    (L.map fun x => Min.min 1 |x.exact v|).prod ≤ (L.map fun x => |x.exact v|).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    have h0 : 0 ≤ (L.map fun x => Min.min 1 |x.exact v|).prod :=
      List.prod_nonneg fun y hy => by
        obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact le_min zero_le_one (abs_nonneg _)
    exact mul_le_mul (min_le_right _ _) ih h0 (abs_nonneg _)

lemma prod_min_bounds (L : List GExpr) (v : ℕ → ℝ) :
    0 ≤ (L.map fun x => Min.min 1 |x.exact v|).prod ∧
      (L.map fun x => Min.min 1 |x.exact v|).prod ≤ 1 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg (le_min zero_le_one (abs_nonneg _)) ih.1,
      (mul_le_mul (min_le_left _ _) ih.2 ih.1 zero_le_one).trans (by norm_num)⟩

/-- A product of divisors: if each factor has relative error at most `ρᵢ`
and the factors' magnitudes, capped at `1`, multiply to at least `2⁻¹⁰⁰`,
every association has relative error at most `Π(1+ρᵢ) (1+U')ᵐ⁻¹ - 1`. -/
theorem mul_group (v E : ℕ → ℝ) : ∀ y : GExpr,
    (∀ x ∈ mulLeaves y, x.Safe v E ∧ 0 ≤ x.bound v E ∧ 0 < |x.exact v|) →
    1/2^100 ≤ ((mulLeaves y).map fun x => Min.min 1 |x.exact v|).prod →
    y.Safe v E ∧ 0 ≤ y.bound v E ∧ y.bound v E ≤ |y.exact v| *
      (((mulLeaves y).map fun x => 1+x.bound v E/|x.exact v|).prod*(1+U')^((mulLeaves y).length-1)-1)
  | .mul a b, h, hm => by
    have hU := WgslPoly.U_pos; have hη := η_pos; have hU' := U'_pos
    have ha : ∀ x ∈ mulLeaves a, x.Safe v E ∧ 0 ≤ x.bound v E ∧ 0 < |x.exact v| :=
      fun x hx => h x (by simp only [mulLeaves]; exact List.mem_append_left _ hx)
    have hb : ∀ x ∈ mulLeaves b, x.Safe v E ∧ 0 ≤ x.bound v E ∧ 0 < |x.exact v| :=
      fun x hx => h x (by simp only [mulLeaves]; exact List.mem_append_right _ hx)
    simp only [mulLeaves, List.map_append, List.prod_append] at hm
    have pa := prod_min_bounds (mulLeaves a) v; have pb := prod_min_bounds (mulLeaves b) v
    have hma : 1/2^100 ≤ ((mulLeaves a).map fun x => Min.min 1 |x.exact v|).prod := by nlinarith
    have hmb : 1/2^100 ≤ ((mulLeaves b).map fun x => Min.min 1 |x.exact v|).prod := by nlinarith
    obtain ⟨sa, ba0, ba⟩ := mul_group v E a ha hma
    obtain ⟨sb, bb0, bb⟩ := mul_group v E b hb hmb
    have na := mulLeaves_length_pos a; have nb := mulLeaves_length_pos b
    set A := |exact v a|; set B := |exact v b|
    set Pa := ((mulLeaves a).map fun x => 1+x.bound v E/|x.exact v|).prod
    set Pb := ((mulLeaves b).map fun x => 1+x.bound v E/|x.exact v|).prod
    have hPa : 1 ≤ Pa := prod_one_le _ _ fun x hx => div_nonneg (ha x hx).2.1 (abs_nonneg _)
    have hPb : 1 ≤ Pb := prod_one_le _ _ fun x hx => div_nonneg (hb x hx).2.1 (abs_nonneg _)
    set Xa := Pa*(1+U')^((mulLeaves a).length-1)
    set Xb := Pb*(1+U')^((mulLeaves b).length-1)
    have hXa : 1 ≤ Xa := one_le_mul_of_one_le_of_one_le hPa (one_le_pow₀ (by linarith))
    have hXb : 1 ≤ Xb := one_le_mul_of_one_le_of_one_le hPb (one_le_pow₀ (by linarith))
    have hAB : 1/2^100 ≤ A*B := by
      have e1 : A = ((mulLeaves a).map fun x => |x.exact v|).prod := by
        simp only [A]; rw [mul_exact v a, abs_prod_map]
      have e2 : B = ((mulLeaves b).map fun x => |x.exact v|).prod := by
        simp only [B]; rw [mul_exact v b, abs_prod_map]
      rw [e1, e2]
      exact hm.trans (mul_le_mul (prod_min_le _ v) (prod_min_le _ v) pb.1
        (List.prod_nonneg fun y hy => by obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; exact abs_nonneg _))
    have hA0 : 0 ≤ A := abs_nonneg _
    have hB0 : 0 ≤ B := abs_nonneg _
    have e1 : A+bound v E a ≤ A*Xa := by nlinarith
    have e2 : B+bound v E b ≤ B*Xb := by nlinarith
    have e3 := mul_le_mul e1 e2 (by positivity) (by positivity)
    have e4 := η_absorb hAB
    have e5 : (U'-WgslPoly.U)*(A*B) ≤ (U'-WgslPoly.U)*(A*B*(Xa*Xb)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hXa hXb))
        (by rw [show U'-WgslPoly.U = 1/2^26 by unfold U'; ring]; positivity)
    refine ⟨⟨sa, sb⟩, by simp only [bound]; positivity, ?_⟩
    simp only [bound, exact, abs_mul, mulLeaves, List.map_append, List.prod_append,
      List.length_append]
    rw [show (mulLeaves a).length+(mulLeaves b).length-1 =
      ((mulLeaves a).length-1)+((mulLeaves b).length-1)+1 by omega, pow_add, pow_add, pow_one]
    have hUU : (1+WgslPoly.U)*((A*Xa)*(B*Xb)) ≤ (1+U')*((A*Xa)*(B*Xb)) - (U'-WgslPoly.U)*(A*B*(Xa*Xb)) := by
      nlinarith
    nlinarith
  | .input _, h, _ | .const _, h, _ | .add _ _, h, _ | .sub _ _, h, _ | .neg _, h, _
  | .div _ _, h, _ | .sqrt _, h, _ | .max _ _, h, _ | .min _ _, h, _ | .lt _ _ _ _, h, _
  | .abs _, h, _ | .invsqrt _, h, _ | .exp _, h, _ | .exp2 _, h, _ | .log _, h, _ | .log2 _, h, _
  | .inh _ _, h, _ | .tanh _ _, h, _ | .lt2 _ _ _ _, h, _ | .sinS _, h, _ | .cosS _, h, _
  | .scale _ _, h, _ | .round _, h, _ | .qsel _ _ _ _, h, _ => by
    simp only [mulLeaves, List.mem_singleton, forall_eq] at h ⊢
    refine ⟨h.1, h.2.1, ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.length_singleton, Nat.sub_self, pow_zero]
    rw [mul_sub, mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt h.2.2)]; linarith

/-! Products over the factors of a chain: numerators enter through `|t|+B`,
divisors through `|t|` and their relative errors `B/|t|`. -/

def lp (L : List (Bool × GExpr)) (f : Bool × GExpr → ℝ) : ℝ := (L.map f).prod

lemma lp_append (L₁ L₂ : List (Bool × GExpr)) (f : Bool × GExpr → ℝ) :
    lp (L₁ ++ L₂) f = lp L₁ f*lp L₂ f := by simp [lp]

lemma lp_divs (L : List GExpr) (f : Bool × GExpr → ℝ) :
    lp (L.map fun x => (true, x)) f = (L.map fun x => f (true, x)).prod := by
  simp [lp, Function.comp_def]

lemma lp_nonneg {L : List (Bool × GExpr)} {f : Bool × GExpr → ℝ} (h : ∀ p ∈ L, 0 ≤ f p) :
    0 ≤ lp L f := List.prod_nonneg fun y hy => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact h p hp

lemma lp_one_le {L : List (Bool × GExpr)} {f : Bool × GExpr → ℝ} (h : ∀ p ∈ L, 1 ≤ f p) :
    1 ≤ lp L f := by
  induction L with
  | nil => simp [lp]
  | cons x L ih =>
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    have h1 := h x (by simp); have h2 := ih fun y hy => h y (by simp [hy])
    nlinarith

lemma lp_le_one {L : List (Bool × GExpr)} {f : Bool × GExpr → ℝ} (h : ∀ p ∈ L, 0 ≤ f p ∧ f p ≤ 1) :
    lp L f ≤ 1 := by
  induction L with
  | nil => simp [lp]
  | cons x L ih =>
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    have h1 := h x (by simp); have h2 := ih fun y hy => h y (by simp [hy])
    exact (mul_le_mul h1.2 h2 (List.prod_nonneg fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact (h p (by simp [hp])).1) zero_le_one).trans
      (by norm_num)

lemma lp_mono {L : List (Bool × GExpr)} {f g : Bool × GExpr → ℝ} (h0 : ∀ p ∈ L, 0 ≤ f p)
    (h : ∀ p ∈ L, f p ≤ g p) : lp L f ≤ lp L g := by
  induction L with
  | nil => simp [lp]
  | cons x L ih =>
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_le_mul (h x (by simp)) (ih (fun y hy => h0 y (by simp [hy])) fun y hy => h y (by simp [hy]))
      (lp_nonneg fun y hy => h0 y (by simp [hy])) ((h0 x (by simp)).trans (h x (by simp)))

section Leaf
variable (v E : ℕ → ℝ)
def nψ (p : Bool × GExpr) : ℝ := if p.1 then 1 else |p.2.exact v|+p.2.bound v E
def nM (p : Bool × GExpr) : ℝ := if p.1 then 1 else Max.max 1 (|p.2.exact v|+p.2.bound v E)
def nT (p : Bool × GExpr) : ℝ := if p.1 then 1 else |p.2.exact v|
def dT (p : Bool × GExpr) : ℝ := if p.1 then |p.2.exact v| else 1
def dP (p : Bool × GExpr) : ℝ := if p.1 then 1+p.2.bound v E/|p.2.exact v| else 1
def dmin (p : Bool × GExpr) : ℝ := if p.1 then Min.min 1 |p.2.exact v| else 1
def dmax (p : Bool × GExpr) : ℝ := if p.1 then Max.max 1 |p.2.exact v| else 1
def dIM (p : Bool × GExpr) : ℝ := if p.1 then Max.max 1 (1/|p.2.exact v|) else 1
end Leaf

/-- The number of divisors. -/
def nd (L : List (Bool × GExpr)) : ℕ := L.countP (·.1)

/-- The divisors' combined relative error factor and the chain's margin. -/
def XD (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ := lp L (dP v E)*(1+U')^(nd L-1)
def cD (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ := 2-XD v E L

lemma abs_prod_exact (v : ℕ → ℝ) (e : GExpr) :
    |e.exact v| = lp (prodLeaves e) (nT v)/lp (prodLeaves e) (dT v) := by
  rw [prod_exact v e]
  induction prodLeaves e with
  | nil => simp [lp]
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul, lp] at ih ⊢
    rw [ih]
    obtain ⟨s, x⟩ := p
    cases s <;> simp [fval, nT, dT, abs_inv] <;> ring

lemma nd_append (L₁ L₂ : List (Bool × GExpr)) : nd (L₁ ++ L₂) = nd L₁+nd L₂ := by
  simp [nd, List.countP_append]

lemma nd_divs (L : List GExpr) : nd (L.map fun x => (true, x)) = L.length := by
  simp [nd, List.countP_map, Function.comp_def]

lemma nd_le (L : List (Bool × GExpr)) : nd L ≤ L.length := List.countP_le_length

section Facts
variable {v E : ℕ → ℝ} {L : List (Bool × GExpr)}

/-- The leaf conditions of a chain. -/
def LeafOK (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : Prop :=
  (∀ p ∈ L, p.2.Safe v E ∧ 0 ≤ p.2.bound v E) ∧ ∀ p ∈ L, p.1 = true → 0 < |p.2.exact v|

lemma LeafOK.dP (h : LeafOK v E L) : ∀ p ∈ L, 1 ≤ dP v E p := fun p hp => by
  unfold WgslReassoc.dP; split_ifs
  · have := (h.1 p hp).2; have := abs_nonneg (p.2.exact v)
    linarith [div_nonneg (h.1 p hp).2 (abs_nonneg (p.2.exact v))]
  · exact le_rfl

lemma one_le_XD (h : LeafOK v E L) : 1 ≤ XD v E L :=
  one_le_mul_of_one_le_of_one_le (lp_one_le h.dP) (one_le_pow₀ (by have := U'_pos; linarith))

lemma nψ_nonneg (h : LeafOK v E L) : ∀ p ∈ L, 0 ≤ nψ v E p := fun p hp => by
  unfold nψ; split_ifs
  · exact zero_le_one
  · have := (h.1 p hp).2; positivity

lemma nψ_le_nM : ∀ p : Bool × GExpr, nψ v E p ≤ nM v E p := fun p => by
  unfold nψ nM; split_ifs
  · exact le_rfl
  · exact le_max_right _ _

lemma one_le_nM : ∀ p : Bool × GExpr, 1 ≤ nM v E p := fun p => by
  unfold nM; split_ifs
  · exact le_rfl
  · exact le_max_left _ _

lemma one_le_dIM : ∀ p : Bool × GExpr, 1 ≤ dIM v p := fun p => by
  unfold dIM; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma one_le_dmax : ∀ p : Bool × GExpr, 1 ≤ dmax v p := fun p => by
  unfold dmax; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma dmin_bounds : ∀ p : Bool × GExpr, 0 ≤ dmin v p ∧ dmin v p ≤ 1 := fun p => by
  unfold dmin; split_ifs
  · exact ⟨le_min zero_le_one (abs_nonneg _), min_le_left _ _⟩
  · exact ⟨zero_le_one, le_rfl⟩

lemma dT_pos (h : LeafOK v E L) : ∀ p ∈ L, 0 < dT v p := fun p hp => by
  unfold dT; split_ifs with hs
  · exact h.2 p hp hs
  · exact zero_lt_one

lemma inv_dT_le_dIM : ∀ p : Bool × GExpr, 1/dT v p ≤ dIM v p := fun p => by
  unfold dT dIM; split_ifs
  · exact le_max_right _ _
  · norm_num

lemma dmin_le_dT : ∀ p : Bool × GExpr, dmin v p ≤ dT v p := fun p => by
  unfold dmin dT; split_ifs
  · exact min_le_right _ _
  · exact le_rfl

lemma dT_le_dmax : ∀ p : Bool × GExpr, dT v p ≤ dmax v p := fun p => by
  unfold dT dmax; split_ifs
  · exact le_max_right _ _
  · exact le_rfl

end Facts

lemma XD_append {v E : ℕ → ℝ} {L₁ L₂ : List (Bool × GExpr)} (h₁ : LeafOK v E L₁) (h₂ : LeafOK v E L₂) :
    XD v E L₁*XD v E L₂ ≤ XD v E (L₁ ++ L₂) := by
  unfold XD
  rw [lp_append, nd_append]
  have p1 := lp_one_le h₁.dP; have p2 := lp_one_le h₂.dP
  have hU : (1:ℝ) ≤ 1+U' := by have := U'_pos; linarith
  have e : (1+U')^(nd L₁-1)*(1+U')^(nd L₂-1) ≤ (1+U')^(nd L₁+nd L₂-1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hU (by omega)
  calc lp L₁ (dP v E)*(1+U')^(nd L₁-1)*(lp L₂ (dP v E)*(1+U')^(nd L₂-1))
      = lp L₁ (dP v E)*lp L₂ (dP v E)*((1+U')^(nd L₁-1)*(1+U')^(nd L₂-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e (by positivity)

lemma cD_append {v E : ℕ → ℝ} {L₁ L₂ : List (Bool × GExpr)} (h₁ : LeafOK v E L₁) (h₂ : LeafOK v E L₂) :
    cD v E (L₁ ++ L₂) ≤ cD v E L₁*cD v E L₂ := by
  unfold cD
  have := XD_append h₁ h₂; have x1 := one_le_XD h₁; have x2 := one_le_XD h₂
  nlinarith

/-- The chain's main term and its `η` weight. -/
def Rf (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ := lp L (nψ v E)/(lp L (dT v)*cD v E L)
def Mf (v E : ℕ → ℝ) (L : List (Bool × GExpr)) : ℝ :=
  lp L (nM v E)*lp L (dIM v)/cD v E L^(nd L)

lemma inv_lp_dT_le {v E : ℕ → ℝ} {L : List (Bool × GExpr)} (h : LeafOK v E L) :
    1/lp L (dT v) ≤ lp L (dIM v) := by
  induction L with
  | nil => simp [lp]
  | cons p L ih =>
    have h' : LeafOK v E L := ⟨fun q hq => h.1 q (by simp [hq]), fun q hq => h.2 q (by simp [hq])⟩
    have t0 := dT_pos h p (by simp)
    have t1 : 0 < lp L (dT v) := List.prod_pos fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos h' q hq
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    calc 1/(dT v p*(L.map (dT v)).prod) = (1/dT v p)*(1/(L.map (dT v)).prod) := by
          rw [one_div_mul_one_div]
      _ ≤ dIM v p*(L.map (dIM v)).prod :=
          mul_le_mul (inv_dT_le_dIM p) (ih h') (by simp only [lp] at t1; exact (one_div_pos.mpr t1).le)
            (by linarith [one_le_dIM (v := v) p])

lemma cD_pow_le {v E : ℕ → ℝ} {L : List (Bool × GExpr)} (h : LeafOK v E L) (hc : 0 < cD v E L) :
    cD v E L^(nd L) ≤ cD v E L := by
  rcases Nat.eq_zero_or_pos (nd L) with h0 | h0
  · have hall : ∀ p ∈ L, p.1 = false := by
      intro p hp; by_contra hne
      have : 0 < nd L := List.countP_pos_iff.mpr ⟨p, hp, by simpa using hne⟩
      omega
    have : lp L (dP v E) = 1 := by
      unfold lp
      rw [List.prod_eq_one]; intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      simp [dP, hall p hp]
    rw [h0, pow_zero]; unfold cD XD; rw [this, h0]; norm_num
  · have h1 : cD v E L ≤ 1 := by unfold cD; linarith [one_le_XD h]
    calc cD v E L^(nd L) ≤ cD v E L^1 := pow_le_pow_of_le_one hc.le h1 h0
      _ = cD v E L := pow_one _

lemma Rf_le_Mf {v E : ℕ → ℝ} {L : List (Bool × GExpr)} (h : LeafOK v E L) (hc : 0 < cD v E L) :
    Rf v E L ≤ Mf v E L := by
  unfold Rf Mf
  have t0 : 0 < lp L (dT v) := List.prod_pos fun y hy => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos h q hq
  have n1 := lp_mono (nψ_nonneg h) (fun p _ => nψ_le_nM (v := v) (E := E) p)
  have n0 := lp_nonneg (nψ_nonneg h)
  have i1 := inv_lp_dT_le h
  have cp := cD_pow_le h hc
  have cp0 : 0 < cD v E L^(nd L) := pow_pos hc _
  rw [div_le_div_iff₀ (mul_pos t0 hc) cp0]
  have i2 : 1 ≤ lp L (dIM v)*lp L (dT v) := by
    have h3 := mul_le_mul_of_nonneg_right i1 t0.le
    rwa [one_div_mul_cancel t0.ne'] at h3
  have m0 : 0 ≤ lp L (nM v E)*cD v E L := mul_nonneg (n0.trans n1) hc.le
  calc lp L (nψ v E)*cD v E L^(nd L) ≤ lp L (nM v E)*cD v E L :=
        mul_le_mul n1 cp cp0.le (n0.trans n1)
    _ ≤ lp L (nM v E)*cD v E L*(lp L (dIM v)*lp L (dT v)) := le_mul_of_one_le_right m0 i2
    _ = lp L (nM v E)*lp L (dIM v)*(lp L (dT v)*cD v E L) := by ring

set_option maxHeartbeats 8000000 in
/-- Every association of a product chain that keeps each factor in its
role: if the factors are `Safe`, the divisors are nonzero and the divisor
margins hold, the chain is `Safe` and its running bound plus its magnitude is
at most `(1+U)ⁿ⁻¹ (Rf + 2(n-1) η Mf)`. -/
theorem prod_bound (v E : ℕ → ℝ) : ∀ x : GExpr, LeafOK v E (prodLeaves x) →
    XD v E (prodLeaves x) < 2 →
    1/2^100 ≤ lp (prodLeaves x) (dmin v) →
    1/2^126 ≤ lp (prodLeaves x) (dmin v)*cD v E (prodLeaves x) →
    lp (prodLeaves x) (dmax v)*XD v E (prodLeaves x) ≤ 2^126 →
    4*((prodLeaves x).length:ℝ)^2*η*(1+WgslPoly.U)^(prodLeaves x).length*Mf v E (prodLeaves x) ≤ 1 →
    x.Safe v E ∧ 0 ≤ x.bound v E ∧
      x.bound v E+|x.exact v| ≤ (1+WgslPoly.U)^((prodLeaves x).length-1)*
        (Rf v E (prodLeaves x)+2*(((prodLeaves x).length:ℝ)-1)*η*Mf v E (prodLeaves x))
  | .mul a b, hl, hX, hm, hlo, hhi, hη => by
    have hU := WgslPoly.U_pos; have hη0 := η_pos
    have eL : prodLeaves (.mul a b) = prodLeaves a ++ prodLeaves b := rfl
    rw [eL] at hl hX hm hlo hhi hη ⊢
    have hla : LeafOK v E (prodLeaves a) :=
      ⟨fun p hp => hl.1 p (List.mem_append_left _ hp), fun p hp => hl.2 p (List.mem_append_left _ hp)⟩
    have hlb : LeafOK v E (prodLeaves b) :=
      ⟨fun p hp => hl.1 p (List.mem_append_right _ hp), fun p hp => hl.2 p (List.mem_append_right _ hp)⟩
    set La := prodLeaves a; set Lb := prodLeaves b
    have xa := one_le_XD hla; have xb := one_le_XD hlb
    have xab := XD_append hla hlb
    have hXa : XD v E La < 2 := by nlinarith
    have hXb : XD v E Lb < 2 := by nlinarith
    have ca0 : 0 < cD v E La := by unfold cD; linarith
    have cb0 : 0 < cD v E Lb := by unfold cD; linarith
    have c0 : 0 < cD v E (La ++ Lb) := by unfold cD; linarith
    have ca1 : cD v E La ≤ 1 := by unfold cD; linarith
    have cb1 : cD v E Lb ≤ 1 := by unfold cD; linarith
    have cab := cD_append hla hlb
    have cca : cD v E (La ++ Lb) ≤ cD v E La := cab.trans (mul_le_of_le_one_right ca0.le cb1)
    have ccb : cD v E (La ++ Lb) ≤ cD v E Lb := cab.trans (mul_le_of_le_one_left cb0.le ca1)
    rw [lp_append] at hm hlo hhi
    have dma := lp_le_one (L := La) (f := dmin v) fun p _ => dmin_bounds p
    have dmb := lp_le_one (L := Lb) (f := dmin v) fun p _ => dmin_bounds p
    have dma0 := lp_nonneg (L := La) (f := dmin v) fun p _ => (dmin_bounds p).1
    have dmb0 := lp_nonneg (L := Lb) (f := dmin v) fun p _ => (dmin_bounds p).1
    have dxa := lp_one_le (L := La) (f := dmax v) fun p _ => one_le_dmax p
    have dxb := lp_one_le (L := Lb) (f := dmax v) fun p _ => one_le_dmax p
    have dmA : lp La (dmin v)*lp Lb (dmin v) ≤ lp La (dmin v) := mul_le_of_le_one_right dma0 dmb
    have dmB : lp La (dmin v)*lp Lb (dmin v) ≤ lp Lb (dmin v) := mul_le_of_le_one_left dmb0 dma
    have hma : 1/2^100 ≤ lp La (dmin v) := hm.trans dmA
    have hmb : 1/2^100 ≤ lp Lb (dmin v) := hm.trans dmB
    have hloa : 1/2^126 ≤ lp La (dmin v)*cD v E La :=
      hlo.trans (mul_le_mul dmA cca c0.le dma0)
    have hlob : 1/2^126 ≤ lp Lb (dmin v)*cD v E Lb :=
      hlo.trans (mul_le_mul dmB ccb c0.le dmb0)
    have hxa' : XD v E La ≤ XD v E (La ++ Lb) := (le_mul_of_one_le_right (by linarith) xb).trans xab
    have hxb' : XD v E Lb ≤ XD v E (La ++ Lb) := (le_mul_of_one_le_left (by linarith) xa).trans xab
    have hhia : lp La (dmax v)*XD v E La ≤ 2^126 :=
      (mul_le_mul (le_mul_of_one_le_right (by linarith) dxb) hxa' (by linarith) (by positivity)).trans hhi
    have hhib : lp Lb (dmax v)*XD v E Lb ≤ 2^126 :=
      (mul_le_mul (le_mul_of_one_le_left (by linarith) dxa) hxb' (by linarith) (by positivity)).trans hhi
    -- the `η` weights
    have nMa := lp_one_le (L := La) (f := nM v E) fun p _ => one_le_nM p
    have nMb := lp_one_le (L := Lb) (f := nM v E) fun p _ => one_le_nM p
    have dIa := lp_one_le (L := La) (f := dIM v) fun p _ => one_le_dIM p
    have dIb := lp_one_le (L := Lb) (f := dIM v) fun p _ => one_le_dIM p
    have pa : cD v E (La ++ Lb)^(nd La) ≤ cD v E La^(nd La) := pow_le_pow_left₀ c0.le cca _
    have pb : cD v E (La ++ Lb)^(nd Lb) ≤ cD v E Lb^(nd Lb) := pow_le_pow_left₀ c0.le ccb _
    have pab : cD v E (La ++ Lb)^(nd (La ++ Lb)) = cD v E (La ++ Lb)^(nd La)*cD v E (La ++ Lb)^(nd Lb) := by
      rw [nd_append, pow_add]
    have c1 : cD v E (La ++ Lb) ≤ 1 := cca.trans ca1
    have pa1 : cD v E (La ++ Lb)^(nd La) ≤ 1 := pow_le_one₀ c0.le c1
    have pb1 : cD v E (La ++ Lb)^(nd Lb) ≤ 1 := pow_le_one₀ c0.le c1
    have pa0 : 0 < cD v E (La ++ Lb)^(nd La) := pow_pos c0 _
    have pb0 : 0 < cD v E (La ++ Lb)^(nd Lb) := pow_pos c0 _
    have MaMb : Mf v E La*Mf v E Lb ≤ Mf v E (La ++ Lb) := by
      unfold Mf; rw [lp_append, lp_append, pab]
      rw [div_mul_div_comm]
      apply div_le_div₀ (by positivity) (le_of_eq (by ring)) (mul_pos pa0 pb0) (mul_le_mul pa pb pb0.le (by positivity))
    have Ma1 : 1 ≤ Mf v E La := by
      unfold Mf; rw [le_div_iff₀ (pow_pos ca0 _), one_mul]
      exact (pow_le_one₀ ca0.le ca1).trans (one_le_mul_of_one_le_of_one_le nMa dIa)
    have Mb1 : 1 ≤ Mf v E Lb := by
      unfold Mf; rw [le_div_iff₀ (pow_pos cb0 _), one_mul]
      exact (pow_le_one₀ cb0.le cb1).trans (one_le_mul_of_one_le_of_one_le nMb dIb)
    have Ma_le : Mf v E La ≤ Mf v E (La ++ Lb) := (le_mul_of_one_le_right (by linarith) Mb1).trans MaMb
    have Mb_le : Mf v E Lb ≤ Mf v E (La ++ Lb) := (le_mul_of_one_le_left (by linarith) Ma1).trans MaMb
    have M1 : 1 ≤ Mf v E (La ++ Lb) := Ma1.trans Ma_le
    have na : 0 < La.length := prodLeaves_length_pos a
    have nb : 0 < Lb.length := prodLeaves_length_pos b
    rw [List.length_append] at hη ⊢
    set n := La.length+Lb.length
    have hU1 : (1:ℝ) ≤ 1+WgslPoly.U := by linarith
    have hηa : 4*(La.length:ℝ)^2*η*(1+WgslPoly.U)^La.length*Mf v E La ≤ 1 := by
      refine le_trans ?_ hη
      have l1 : (La.length:ℝ)^2 ≤ (n:ℝ)^2 := by
        have : (La.length:ℝ) ≤ n := by exact_mod_cast Nat.le_add_right La.length Lb.length
        exact pow_le_pow_left₀ (by positivity) this 2
      have l2 : (1+WgslPoly.U)^La.length ≤ (1+WgslPoly.U)^n := pow_le_pow_right₀ hU1 (by omega)
      gcongr
    have hηb : 4*(Lb.length:ℝ)^2*η*(1+WgslPoly.U)^Lb.length*Mf v E Lb ≤ 1 := by
      refine le_trans ?_ hη
      have l1 : (Lb.length:ℝ)^2 ≤ (n:ℝ)^2 := by
        have : (Lb.length:ℝ) ≤ n := by exact_mod_cast Nat.le_add_left Lb.length La.length
        exact pow_le_pow_left₀ (by positivity) this 2
      have l2 : (1+WgslPoly.U)^Lb.length ≤ (1+WgslPoly.U)^n := pow_le_pow_right₀ hU1 (by omega)
      gcongr
    obtain ⟨sa, ba0, ia⟩ := prod_bound v E a hla hXa hma hloa hhia hηa
    obtain ⟨sb, bb0, ib⟩ := prod_bound v E b hlb hXb hmb hlob hhib hηb
    refine ⟨⟨sa, sb⟩, by simp only [bound]; positivity, ?_⟩
    -- main term
    have ra0 : 0 ≤ Rf v E La := div_nonneg (lp_nonneg (nψ_nonneg hla))
      (mul_nonneg (lp_nonneg fun p hp => (dT_pos hla p hp).le) ca0.le)
    have rb0 : 0 ≤ Rf v E Lb := div_nonneg (lp_nonneg (nψ_nonneg hlb))
      (mul_nonneg (lp_nonneg fun p hp => (dT_pos hlb p hp).le) cb0.le)
    have RaRb : Rf v E La*Rf v E Lb ≤ Rf v E (La ++ Lb) := by
      unfold Rf; rw [lp_append, lp_append, div_mul_div_comm]
      have t0 : 0 < lp La (dT v)*lp Lb (dT v) := mul_pos
        (List.prod_pos fun y hy => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos hla q hq)
        (List.prod_pos fun y hy => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos hlb q hq)
      apply div_le_div₀ (mul_nonneg (lp_nonneg (nψ_nonneg hla)) (lp_nonneg (nψ_nonneg hlb))) le_rfl
        (mul_pos t0 c0)
      calc lp La (dT v)*lp Lb (dT v)*cD v E (La ++ Lb)
          ≤ lp La (dT v)*lp Lb (dT v)*(cD v E La*cD v E Lb) := mul_le_mul_of_nonneg_left cab t0.le
        _ = lp La (dT v)*cD v E La*(lp Lb (dT v)*cD v E Lb) := by ring
    have RMa := Rf_le_Mf hla ca0
    have RMb := Rf_le_Mf hlb cb0
    set Ka := (1+WgslPoly.U)^(La.length-1)
    set Kb := (1+WgslPoly.U)^(Lb.length-1)
    have hK : (1+WgslPoly.U)^(n-1) = (1+WgslPoly.U)*Ka*Kb := by
      simp only [Ka, Kb, n]; rw [← pow_succ', ← pow_add]; congr 1; omega
    have Ka1 : 1 ≤ Ka := one_le_pow₀ hU1
    have Kb1 : 1 ≤ Kb := one_le_pow₀ hU1
    set Ra := Rf v E La; set Rb := Rf v E Lb; set Ma := Mf v E La; set Mb := Mf v E Lb
    set R := Rf v E (La ++ Lb); set M := Mf v E (La ++ Lb)
    have αa : (0:ℝ) ≤ 2*((La.length:ℝ)-1)*η := by
      have : (1:ℝ) ≤ La.length := by exact_mod_cast na
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη0.le
    have αb : (0:ℝ) ≤ 2*((Lb.length:ℝ)-1)*η := by
      have : (1:ℝ) ≤ Lb.length := by exact_mod_cast nb
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη0.le
    set α := 2*((La.length:ℝ)-1)*η; set β := 2*((Lb.length:ℝ)-1)*η
    have Ψa : |exact v a|+bound v E a ≤ Ka*(Ra+α*Ma) := by linarith
    have Ψb : |exact v b|+bound v E b ≤ Kb*(Rb+β*Mb) := by linarith
    have hprod := mul_le_mul Ψa Ψb (by positivity) (by positivity)
    -- the cross term `α β Ma Mb` is at most `η`
    have hKn : (1+WgslPoly.U)^(n-1) ≤ (1+WgslPoly.U)^n := pow_le_pow_right₀ hU1 (by omega)
    have hab : α*β*(Ma*Mb)*((1+WgslPoly.U)^(n-1)) ≤ η := by
      have l1 : ((La.length:ℝ)-1)*((Lb.length:ℝ)-1) ≤ (n:ℝ)^2 := by
        simp only [n]; push_cast; nlinarith
      have e : α*β*(Ma*Mb)*((1+WgslPoly.U)^(n-1)) =
          η*(4*(((La.length:ℝ)-1)*((Lb.length:ℝ)-1))*η*((1+WgslPoly.U)^(n-1))*(Ma*Mb)) := by
        simp only [α, β]; ring
      rw [e]
      refine mul_le_of_le_one_right hη0.le (le_trans ?_ hη)
      have : 0 ≤ ((La.length:ℝ)-1)*((Lb.length:ℝ)-1) := by
        have : (1:ℝ) ≤ La.length := by exact_mod_cast na
        have : (1:ℝ) ≤ Lb.length := by exact_mod_cast nb
        nlinarith
      gcongr
    have hexp : bound v E (.mul a b)+|exact v (.mul a b)| =
        (1+WgslPoly.U)*((|exact v a|+bound v E a)*(|exact v b|+bound v E b))+η := by
      simp only [bound, exact, abs_mul]; ring
    rw [hexp, hK]
    have h1 : Ra*Mb ≤ M := (mul_le_mul_of_nonneg_right RMa (by linarith)).trans MaMb
    have h2 : Ma*Rb ≤ M := (mul_le_mul_of_nonneg_left RMb (by linarith)).trans MaMb
    have hα : α+β+2*η = 2*((n:ℝ)-1)*η := by simp only [α, β, n]; push_cast; ring
    have K0 : 1 ≤ (1+WgslPoly.U)*Ka*Kb :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hU1 Ka1) Kb1
    calc (1+WgslPoly.U)*((|exact v a|+bound v E a)*(|exact v b|+bound v E b))+η
        ≤ (1+WgslPoly.U)*(Ka*(Ra+α*Ma)*(Kb*(Rb+β*Mb)))+η := by gcongr
      _ = (1+WgslPoly.U)*Ka*Kb*(Ra*Rb+β*(Ra*Mb)+α*(Ma*Rb))+α*β*(Ma*Mb)*((1+WgslPoly.U)*Ka*Kb)+η := by
          ring
      _ ≤ (1+WgslPoly.U)*Ka*Kb*(R+β*M+α*M)+η+η := by
          rw [hK] at hab
          gcongr
      _ ≤ (1+WgslPoly.U)*Ka*Kb*(R+2*((n:ℝ)-1)*η*M) := by
          rw [← hα]
          have e1 : 2*η ≤ 2*η*((1+WgslPoly.U)*Ka*Kb*M) :=
            le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le K0 M1)
          have e2 : (1+WgslPoly.U)*Ka*Kb*(R+(α+β+2*η)*M) =
              (1+WgslPoly.U)*Ka*Kb*(R+β*M+α*M)+2*η*((1+WgslPoly.U)*Ka*Kb*M) := by ring
          linarith
  | .div a b, hl, hX, hm, hlo, hhi, hη => by
    have hU := WgslPoly.U_pos; have hη0 := η_pos
    have eL : prodLeaves (.div a b) = prodLeaves a ++ (mulLeaves b).map fun x => (true, x) := rfl
    rw [eL] at hl hX hm hlo hhi hη ⊢
    have hla : LeafOK v E (prodLeaves a) :=
      ⟨fun p hp => hl.1 p (List.mem_append_left _ hp), fun p hp => hl.2 p (List.mem_append_left _ hp)⟩
    have hlb : LeafOK v E ((mulLeaves b).map fun x => (true, x)) :=
      ⟨fun p hp => hl.1 p (List.mem_append_right _ hp), fun p hp => hl.2 p (List.mem_append_right _ hp)⟩
    set La := prodLeaves a; set Lb := (mulLeaves b).map fun x => (true, x)
    have xa := one_le_XD hla; have xb := one_le_XD hlb
    have xab := XD_append hla hlb
    have hXa : XD v E La < 2 := by nlinarith
    have hXb : XD v E Lb < 2 := by nlinarith
    have ca0 : 0 < cD v E La := by unfold cD; linarith
    have cb0 : 0 < cD v E Lb := by unfold cD; linarith
    have c0 : 0 < cD v E (La ++ Lb) := by unfold cD; linarith
    have ca1 : cD v E La ≤ 1 := by unfold cD; linarith
    have cb1 : cD v E Lb ≤ 1 := by unfold cD; linarith
    have cab := cD_append hla hlb
    have cca : cD v E (La ++ Lb) ≤ cD v E La := cab.trans (mul_le_of_le_one_right ca0.le cb1)
    have ccb : cD v E (La ++ Lb) ≤ cD v E Lb := cab.trans (mul_le_of_le_one_left cb0.le ca1)
    rw [lp_append] at hm hlo hhi
    have dma := lp_le_one (L := La) (f := dmin v) fun p _ => dmin_bounds p
    have dmb := lp_le_one (L := Lb) (f := dmin v) fun p _ => dmin_bounds p
    have dma0 := lp_nonneg (L := La) (f := dmin v) fun p _ => (dmin_bounds p).1
    have dmb0 := lp_nonneg (L := Lb) (f := dmin v) fun p _ => (dmin_bounds p).1
    have dxa := lp_one_le (L := La) (f := dmax v) fun p _ => one_le_dmax p
    have dxb := lp_one_le (L := Lb) (f := dmax v) fun p _ => one_le_dmax p
    have dmA : lp La (dmin v)*lp Lb (dmin v) ≤ lp La (dmin v) := mul_le_of_le_one_right dma0 dmb
    have dmB : lp La (dmin v)*lp Lb (dmin v) ≤ lp Lb (dmin v) := mul_le_of_le_one_left dmb0 dma
    have hma : 1/2^100 ≤ lp La (dmin v) := hm.trans dmA
    have hmb : 1/2^100 ≤ lp Lb (dmin v) := hm.trans dmB
    have hloa : 1/2^126 ≤ lp La (dmin v)*cD v E La :=
      hlo.trans (mul_le_mul dmA cca c0.le dma0)
    have hxa' : XD v E La ≤ XD v E (La ++ Lb) := (le_mul_of_one_le_right (by linarith) xb).trans xab
    have hxb' : XD v E Lb ≤ XD v E (La ++ Lb) := (le_mul_of_one_le_left (by linarith) xa).trans xab
    have hhia : lp La (dmax v)*XD v E La ≤ 2^126 :=
      (mul_le_mul (le_mul_of_one_le_right (by linarith) dxb) hxa' (by linarith) (by positivity)).trans hhi
    -- the divisor `b`
    have leafb : ∀ x ∈ mulLeaves b, x.Safe v E ∧ 0 ≤ x.bound v E ∧ 0 < |x.exact v| := fun x hx => by
      have hp : (true, x) ∈ Lb := List.mem_map.mpr ⟨x, hx, rfl⟩
      exact ⟨(hlb.1 _ hp).1, (hlb.1 _ hp).2, hlb.2 _ hp rfl⟩
    have eMin : lp Lb (dmin v) = ((mulLeaves b).map fun x => Min.min 1 |x.exact v|).prod := by
      simp only [Lb, lp_divs, dmin, ↓reduceIte]
    have eP : XD v E Lb = ((mulLeaves b).map fun x => 1+x.bound v E/|x.exact v|).prod*
        (1+U')^((mulLeaves b).length-1) := by
      simp only [XD, Lb, lp_divs, dP, ↓reduceIte, nd_divs]
    have eT : |b.exact v| = lp Lb (dT v) := by
      simp only [Lb, lp_divs, dT, ↓reduceIte]; rw [mul_exact v b, abs_prod_map]
    have eMax : lp Lb (dmax v) = ((mulLeaves b).map fun x => Max.max 1 |x.exact v|).prod := by
      simp only [Lb, lp_divs, dmax, ↓reduceIte]
    obtain ⟨sb, bb0, bb⟩ := mul_group v E b leafb (eMin ▸ hmb)
    rw [← eP, eT] at bb
    have tb : 0 < lp Lb (dT v) := List.prod_pos fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos hlb q hq
    have hΛ : lp Lb (dT v)*cD v E Lb ≤ lp Lb (dT v)-bound v E b := by unfold cD; nlinarith
    have Λ0 : 0 < lp Lb (dT v)-bound v E b := lt_of_lt_of_le (mul_pos tb cb0) hΛ
    have tmin : lp Lb (dmin v) ≤ lp Lb (dT v) := lp_mono (fun p _ => (dmin_bounds p).1) fun p _ => dmin_le_dT p
    have tmax : lp Lb (dT v) ≤ lp Lb (dmax v) := lp_mono (fun p hp => (dT_pos hlb p hp).le) fun p _ => dT_le_dmax p
    -- the `η` weights
    have nMa := lp_one_le (L := La) (f := nM v E) fun p _ => one_le_nM p
    have nMb := lp_one_le (L := Lb) (f := nM v E) fun p _ => one_le_nM p
    have dIa := lp_one_le (L := La) (f := dIM v) fun p _ => one_le_dIM p
    have dIb := lp_one_le (L := Lb) (f := dIM v) fun p _ => one_le_dIM p
    have nb1 : 1 ≤ nd Lb := by simp only [Lb, nd_divs]; exact mulLeaves_length_pos b
    have c1 : cD v E (La ++ Lb) ≤ 1 := cca.trans ca1
    have pa : cD v E (La ++ Lb)^(nd La) ≤ cD v E La^(nd La) := pow_le_pow_left₀ c0.le cca _
    have pb : cD v E (La ++ Lb)^(nd Lb) ≤ cD v E (La ++ Lb) :=
      (pow_le_pow_of_le_one c0.le c1 nb1).trans_eq (pow_one _)
    have pab : cD v E (La ++ Lb)^(nd (La ++ Lb)) = cD v E (La ++ Lb)^(nd La)*cD v E (La ++ Lb)^(nd Lb) := by
      rw [nd_append, pow_add]
    have pa0 : 0 < cD v E (La ++ Lb)^(nd La) := pow_pos c0 _
    have pb0 : 0 < cD v E (La ++ Lb)^(nd Lb) := pow_pos c0 _
    have Ma1 : 1 ≤ Mf v E La := by
      unfold Mf; rw [le_div_iff₀ (pow_pos ca0 _), one_mul]
      exact (pow_le_one₀ ca0.le ca1).trans (one_le_mul_of_one_le_of_one_le nMa dIa)
    have nMb1 : lp Lb (nM v E) = 1 := by
      unfold lp; rw [List.prod_eq_one]; intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      simp [nM]
    have nψb1 : lp Lb (nψ v E) = 1 := by
      unfold lp; rw [List.prod_eq_one]; intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      simp [nψ]
    have ib := inv_lp_dT_le hlb
    -- `Ma/Λ ≤ M`
    have MaΛ : Mf v E La/(lp Lb (dT v)*cD v E Lb) ≤ Mf v E (La ++ Lb) := by
      unfold Mf; rw [lp_append, lp_append, pab, nMb1, mul_one]
      rw [div_div, div_le_div_iff₀ (mul_pos (pow_pos ca0 _) (mul_pos tb cb0)) (mul_pos pa0 pb0)]
      have i2 : 1 ≤ lp Lb (dIM v)*lp Lb (dT v) := by
        have h3 := mul_le_mul_of_nonneg_right ib tb.le
        rwa [one_div_mul_cancel tb.ne'] at h3
      have k0 : 0 ≤ lp La (nM v E)*lp La (dIM v) := by positivity
      calc lp La (nM v E)*lp La (dIM v)*(cD v E (La ++ Lb)^(nd La)*cD v E (La ++ Lb)^(nd Lb))
          ≤ lp La (nM v E)*lp La (dIM v)*(cD v E La^(nd La)*cD v E Lb) :=
            mul_le_mul_of_nonneg_left (mul_le_mul pa (pb.trans ccb) pb0.le (pow_pos ca0 _).le) k0
        _ ≤ lp La (nM v E)*lp La (dIM v)*(cD v E La^(nd La)*cD v E Lb)*(lp Lb (dIM v)*lp Lb (dT v)) :=
            le_mul_of_one_le_right (by positivity) i2
        _ = lp La (nM v E)*(lp La (dIM v)*lp Lb (dIM v))*(cD v E La^(nd La)*(lp Lb (dT v)*cD v E Lb)) := by
            ring
    have M1 : 1 ≤ Mf v E (La ++ Lb) := by
      unfold Mf; rw [le_div_iff₀ (pow_pos c0 _), one_mul]
      refine (pow_le_one₀ c0.le c1).trans ?_
      rw [lp_append, lp_append, nMb1, mul_one]
      exact one_le_mul_of_one_le_of_one_le nMa (one_le_mul_of_one_le_of_one_le dIa dIb)
    have Ma_le : Mf v E La ≤ Mf v E (La ++ Lb) := by
      unfold Mf; rw [lp_append, lp_append, pab, nMb1, mul_one]
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) dIb) (by linarith)) (mul_pos pa0 pb0)
      calc cD v E (La ++ Lb)^(nd La)*cD v E (La ++ Lb)^(nd Lb) ≤ cD v E (La ++ Lb)^(nd La) :=
            mul_le_of_le_one_right pa0.le (pow_le_one₀ c0.le c1)
        _ ≤ cD v E La^(nd La) := pa
    have na : 0 < La.length := prodLeaves_length_pos a
    have nb : 0 < Lb.length := by simp only [Lb, List.length_map]; exact mulLeaves_length_pos b
    rw [List.length_append] at hη ⊢
    set n := La.length+Lb.length
    have hU1 : (1:ℝ) ≤ 1+WgslPoly.U := by linarith
    have hηa : 4*(La.length:ℝ)^2*η*(1+WgslPoly.U)^La.length*Mf v E La ≤ 1 := by
      refine le_trans ?_ hη
      have l1 : (La.length:ℝ)^2 ≤ (n:ℝ)^2 := by
        have : (La.length:ℝ) ≤ n := by exact_mod_cast Nat.le_add_right La.length Lb.length
        exact pow_le_pow_left₀ (by positivity) this 2
      have l2 : (1+WgslPoly.U)^La.length ≤ (1+WgslPoly.U)^n := pow_le_pow_right₀ hU1 (by omega)
      have A1 : 4*(La.length:ℝ)^2*η ≤ 4*(n:ℝ)^2*η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left l1 (by norm_num)) hη0.le
      have A2 : 4*(La.length:ℝ)^2*η*(1+WgslPoly.U)^La.length ≤ 4*(n:ℝ)^2*η*(1+WgslPoly.U)^n :=
        mul_le_mul A1 l2 (by positivity) (by positivity)
      exact mul_le_mul A2 Ma_le (by linarith) (by positivity)
    obtain ⟨sa, ba0, ia⟩ := prod_bound v E a hla hXa hma hloa hhia hηa
    have bnd : bound v E b < lp Lb (dT v) := by
      have h1 := mul_pos tb cb0; linarith only [hΛ, h1]
    refine ⟨⟨sa, sb, by rw [eT]; exact bnd, ?_, ?_⟩, ?_, ?_⟩
    · rw [eT]
      calc 1/2^126 ≤ lp La (dmin v)*lp Lb (dmin v)*cD v E (La ++ Lb) := hlo
        _ ≤ lp Lb (dmin v)*cD v E Lb := mul_le_mul dmB ccb c0.le dmb0
        _ ≤ lp Lb (dT v)*cD v E Lb := mul_le_mul_of_nonneg_right tmin cb0.le
        _ ≤ _ := hΛ
    · rw [eT]
      calc lp Lb (dT v)+bound v E b ≤ lp Lb (dT v)*XD v E Lb := by nlinarith
        _ ≤ lp Lb (dmax v)*XD v E (La ++ Lb) := mul_le_mul tmax hxb' (by linarith) (by linarith)
        _ ≤ lp La (dmax v)*lp Lb (dmax v)*XD v E (La ++ Lb) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) dxa) (by linarith)
        _ ≤ 2^126 := hhi
    · simp only [bound]; rw [eT]
      exact add_nonneg (add_nonneg (div_nonneg (add_nonneg ba0 (mul_nonneg (abs_nonneg _) bb0)) Λ0.le)
        (mul_nonneg hU.le (div_nonneg (add_nonneg (abs_nonneg _) ba0) Λ0.le))) hη0.le
    -- main term
    have hexp : bound v E (.div a b)+|exact v (.div a b)| =
        (1+WgslPoly.U)*(|exact v a|+bound v E a)/(lp Lb (dT v)-bound v E b)+η := by
      simp only [bound, exact, abs_div]; rw [eT]
      field_simp
      ring
    rw [hexp]
    have ra0 : 0 ≤ Rf v E La := div_nonneg (lp_nonneg (nψ_nonneg hla))
      (mul_nonneg (lp_nonneg fun p hp => (dT_pos hla p hp).le) ca0.le)
    have RaΛ : Rf v E La/(lp Lb (dT v)*cD v E Lb) ≤ Rf v E (La ++ Lb) := by
      unfold Rf; rw [lp_append, lp_append, nψb1, mul_one, div_div]
      have ta : 0 < lp La (dT v) := List.prod_pos fun y hy => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact dT_pos hla q hq
      apply div_le_div₀ (lp_nonneg (nψ_nonneg hla)) le_rfl (mul_pos (mul_pos ta tb) c0)
      calc lp La (dT v)*lp Lb (dT v)*cD v E (La ++ Lb)
          ≤ lp La (dT v)*lp Lb (dT v)*(cD v E La*cD v E Lb) := mul_le_mul_of_nonneg_left cab (by positivity)
        _ = lp La (dT v)*cD v E La*(lp Lb (dT v)*cD v E Lb) := by ring
    set Ka := (1+WgslPoly.U)^(La.length-1)
    have Ka1 : 1 ≤ Ka := one_le_pow₀ hU1
    have hK : (1+WgslPoly.U)*Ka ≤ (1+WgslPoly.U)^(n-1) := by
      simp only [Ka, n]; rw [← pow_succ']; exact pow_le_pow_right₀ hU1 (by omega)
    set Ra := Rf v E La; set Ma := Mf v E La
    set R := Rf v E (La ++ Lb); set M := Mf v E (La ++ Lb)
    have αa : (0:ℝ) ≤ 2*((La.length:ℝ)-1)*η := by
      have : (1:ℝ) ≤ La.length := by exact_mod_cast na
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη0.le
    set α := 2*((La.length:ℝ)-1)*η
    have Ψa : |exact v a|+bound v E a ≤ Ka*(Ra+α*Ma) := by linarith
    have Λp : 0 < lp Lb (dT v)*cD v E Lb := mul_pos tb cb0
    have hR0 : 0 ≤ R := div_nonneg (lp_nonneg (nψ_nonneg hl))
      (mul_nonneg (lp_nonneg fun p hp => (dT_pos hl p hp).le) c0.le)
    have M0 : 0 ≤ M := by linarith
    have hna : (La.length:ℝ)+1 ≤ n := by
      have : (1:ℝ) ≤ Lb.length := by exact_mod_cast nb
      simp only [n]; push_cast; linarith
    have hα : α ≤ 2*((n:ℝ)-2)*η := by simp only [α]; nlinarith
    have K1 : 1 ≤ (1+WgslPoly.U)^(n-1) := one_le_pow₀ hU1
    have step1 : (1+WgslPoly.U)*(|exact v a|+bound v E a)/(lp Lb (dT v)-bound v E b) ≤
        (1+WgslPoly.U)*Ka*(Ra/(lp Lb (dT v)*cD v E Lb)+α*(Ma/(lp Lb (dT v)*cD v E Lb))) := by
      rw [div_le_iff₀ Λ0]
      have e : (1+WgslPoly.U)*Ka*(Ra/(lp Lb (dT v)*cD v E Lb)+α*(Ma/(lp Lb (dT v)*cD v E Lb)))*
          (lp Lb (dT v)*cD v E Lb) = (1+WgslPoly.U)*(Ka*(Ra+α*Ma)) := by
        field_simp
      have m0 : 0 ≤ (1+WgslPoly.U)*Ka*(Ra/(lp Lb (dT v)*cD v E Lb)+α*(Ma/(lp Lb (dT v)*cD v E Lb))) := by
        have : 0 ≤ Ra/(lp Lb (dT v)*cD v E Lb) := div_nonneg ra0 Λp.le
        have : 0 ≤ Ma/(lp Lb (dT v)*cD v E Lb) := div_nonneg (by linarith) Λp.le
        positivity
      calc (1+WgslPoly.U)*(|exact v a|+bound v E a) ≤ (1+WgslPoly.U)*(Ka*(Ra+α*Ma)) :=
            mul_le_mul_of_nonneg_left Ψa (by linarith)
        _ = _ := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hΛ m0
    calc (1+WgslPoly.U)*(|exact v a|+bound v E a)/(lp Lb (dT v)-bound v E b)+η
        ≤ (1+WgslPoly.U)*Ka*(R+α*M)+η := by
          have := mul_le_mul_of_nonneg_left MaΛ αa
          have h3 : Ra/(lp Lb (dT v)*cD v E Lb)+α*(Ma/(lp Lb (dT v)*cD v E Lb)) ≤ R+α*M := by linarith
          have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (1+WgslPoly.U)*Ka)
          linarith
      _ ≤ (1+WgslPoly.U)^(n-1)*(R+α*M)+η := by
          have : 0 ≤ R+α*M := by positivity
          nlinarith
      _ ≤ (1+WgslPoly.U)^(n-1)*(R+2*((n:ℝ)-1)*η*M) := by
          have e1 : α*M ≤ 2*((n:ℝ)-2)*η*M := mul_le_mul_of_nonneg_right hα M0
          have e2 : η ≤ 2*η*((1+WgslPoly.U)^(n-1)*M) := by
            have : 1 ≤ (1+WgslPoly.U)^(n-1)*M := one_le_mul_of_one_le_of_one_le K1 M1
            nlinarith
          have e3 := mul_le_mul_of_nonneg_left e1 (by linarith : (0:ℝ) ≤ (1+WgslPoly.U)^(n-1))
          nlinarith

  | .input _, hl, _, _, _, _, _ | .const _, hl, _, _, _, _, _ | .add _ _, hl, _, _, _, _, _
  | .sub _ _, hl, _, _, _, _, _ | .neg _, hl, _, _, _, _, _ | .sqrt _, hl, _, _, _, _, _
  | .max _ _, hl, _, _, _, _, _ | .min _ _, hl, _, _, _, _, _ | .lt _ _ _ _, hl, _, _, _, _, _
  | .abs _, hl, _, _, _, _, _ | .invsqrt _, hl, _, _, _, _, _ | .exp _, hl, _, _, _, _, _
  | .exp2 _, hl, _, _, _, _, _ | .log _, hl, _, _, _, _, _ | .log2 _, hl, _, _, _, _, _
  | .inh _ _, hl, _, _, _, _, _ | .tanh _ _, hl, _, _, _, _, _ | .lt2 _ _ _ _, hl, _, _, _, _, _
  | .sinS _, hl, _, _, _, _, _ | .cosS _, hl, _, _, _, _, _ | .scale _ _, hl, _, _, _, _, _
  | .round _, hl, _, _, _, _, _ | .qsel _ _ _ _, hl, _, _, _, _, _ => by
    obtain ⟨h1, -⟩ := hl
    simp only [prodLeaves, List.mem_singleton, forall_eq] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    simp [prodLeaves, Rf, Mf, cD, XD, lp, nψ, dT, nd, dP]
    linarith

end BlackHole.WgslReassoc
