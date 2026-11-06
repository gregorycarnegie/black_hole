module

public import BlackHole.WgslSafeBoxes

/-! A closed-form domain on which every reassociation of `spatial_unit`
satisfies `Safe` (obligation F2), covered by boxes (`WgslSafeBoxes`) with its
quadratic form bounded below by positive definiteness. -/

@[expose] public section

namespace BlackHole.WgslSafeDomains
open Wgsl WgslExpr GExpr WgslPlasma WgslDomain

/-! ### `spatial_unit` -/

/-- `spatial_unit` applied to inputs 100–102 (as in the translation fixture),
with the spatial metric `gamma` read from inputs 5–7, 9–11, 13–15. -/
def suVec (j : Fin 3) : GExpr := input (100+j)
def suScale : GExpr := max (max (abs (suVec 0)) (abs (suVec 1))) (abs (suVec 2))
def suScaled (j : Fin 3) : GExpr := div (suVec j) suScale
def suQ : GExpr := WgslScreen.dot3 suScaled (WgslScreen.gammaMul suScaled)
/-- `spatial_unit` with its quadratic form as a `let` slot (`WgslLets.ref 0`). -/
def suBody (i : Fin 3) : GExpr :=
  lt (neg suScale) 0 (mul (suScaled i) (invsqrt (max (WgslLets.ref 0) (const WgslScreen.f32_1em20))))
    (suVec i)

lemma su_lets (i : Fin 3) : WgslLets.withLets [suQ] (suBody i) = WgslScreen.spatialUnit suVec i := by
  fin_cases i <;> rfl

def gIdx : List ℕ := [5,6,7,9,10,11,13,14,15]

/-- The vector in octave `k` and slab `s`; metric entries in `[-64, 64]` with
errors up to `2⁻¹⁴`. -/
def suEnv (k : ℤ) (s : ℕ) : ℕ → Option Av := fun i =>
  if 100 ≤ i ∧ i < 103 then some (slabAv k s (i-100) (2*pow2 k/1048576))
  else if i ∈ gIdx then some (Av.mk3 (-64) 64 (1/16384)) else none

/-- The quadratic form's interval, raised to `1/32` by positive definiteness. -/
def refineQ (A : Av) : Av := ⟨Max.max A.lo (1/32), A.hi, A.b, A.sc, A.sn, A.sm, A.sb, A.pc, A.pd, A.mc, A.md⟩

def suOk (k : ℤ) (s : ℕ) : Bool :=
  match ev 0 (suEnv k s) suQ with
  | some A => ([0,1,2] : List (Fin 3)).all fun i =>
      (ev 0 (slotEnv (suEnv k s) [refineQ A]) (suBody i)).isSome
  | none => false

set_option maxRecDepth 100000 in
theorem suEnv_ok : ((List.range 41).all fun k => (List.range 6).all fun s => suOk ((k:ℤ)-20) s) = true := by
  decide +kernel

lemma suQ_exact (v : ℕ → ℝ) : suQ.exact v = (∑ i : Fin 3, v (100+i)*
    ∑ j : Fin 3, v (4*(i.succ : ℕ)+j.succ)*v (100+j))/(vmax v 100)^2 := by
  have hm : suScale.exact v = vmax v 100 := rfl
  simp only [suQ, WgslScreen.dot3, WgslScreen.gammaMul, WgslScreen.sum3, WgslScreen.gamma,
    WgslScreen.g, suScaled, exact, hm, suVec, Fin.sum_univ_three]
  simp
  ring

/-- Every reassociation of `spatial_unit` satisfies `Safe`, so its running
bound holds, for every
vector with `2⁻²⁰ ≤ max |vᵢ| ≤ 2²⁰` and component errors up to
`2⁻²⁰ max |vᵢ|`, and every spatial metric with entries in `[-64, 64]`,
entry errors up to `2⁻¹⁴`, and quadratic form at least `max |vᵢ|²/32` at the
vector (for instance, smallest eigenvalue at least `1/32`). -/
theorem spatial_unit_safe (i : Fin 3) (v E : ℕ → ℝ) (h1 : (2:ℝ)^(-20:ℤ) ≤ vmax v 100)
    (h2 : vmax v 100 ≤ (2:ℝ)^(20:ℤ)) (hE : ∀ j, j < 3 → 0 ≤ E (100+j) ∧ E (100+j) ≤ vmax v 100/2^20)
    (hg : ∀ n ∈ gIdx, |v n| ≤ 64 ∧ 0 ≤ E n ∧ E n ≤ 1/16384)
    (hpd : (vmax v 100)^2/32 ≤ ∑ i : Fin 3, v (100+i)*∑ j : Fin 3, v (4*(i.succ : ℕ)+j.succ)*v (100+j)) :
    ∀ x', WgslReassoc.RA (WgslScreen.spatialUnit suVec i) x' → x'.Safe v E := by
  obtain ⟨k, s, kl, kh, hs, hsl, hb⟩ := vec_cover v 100 h1 h2
  have hok := all_range (all_range suEnv_ok (k := (k+20).toNat) (by omega)) hs
  rw [show (((k+20).toNat : ℕ) : ℤ)-20 = k by omega] at hok
  have henv : EnvH (suEnv k s) v E := by
    intro n A hA
    unfold suEnv at hA
    split_ifs at hA with p q <;> simp only [Option.some.injEq] at hA <;> subst hA
    · obtain ⟨j, rfl⟩ : ∃ j, n = 100+j := ⟨n-100, by omega⟩
      have hj : j < 3 := by omega
      obtain ⟨hx, hv⟩ := hb j hj
      obtain ⟨e0, e1⟩ := hE j hj
      rw [show 100+j-100 = j by omega]
      refine slabAv_H hx (hsl j hj).1 (hsl j hj).2 e0 (e1.trans ?_)
      push_cast; rw [pow2_eq]; linarith
    · obtain ⟨hv, e0, e1⟩ := hg n q
      have := abs_le.mp hv
      exact ⟨by push_cast; linarith, by push_cast; linarith, e0, by push_cast; linarith⟩
  have hlow : EnvLow (suEnv k s) := by
    intro n hn; simp only [suEnv]
    split_ifs with p q
    all_goals first | rfl | (exfalso; simp_all [gIdx, WgslLets.letBase]; omega)
  have hm0 : 0 < vmax v 100 := lt_of_lt_of_le (by positivity) h1
  have hqe : 1/32 ≤ suQ.exact v := by
    rw [suQ_exact, le_div_iff₀ (by positivity)]; linarith
  unfold suOk at hok
  cases hQ : ev 0 (suEnv k s) suQ with
  | none => rw [hQ] at hok; simp at hok
  | some A =>
    rw [hQ, List.all_eq_true] at hok
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (hok i (by fin_cases i <;> simp))
    have envR : EnvR (suEnv k s) GExpr.input v E := fun n A' hA' =>
      ⟨fun _ => ⟨rfl, henv n A' hA'⟩, fun hn => by rw [hlow n hn] at hA'; exact absurd hA' (by simp)⟩
    have rQ : RH v E A suQ := by
      have := ev_robust 0 suQ _ _ v E A envR hQ; rwa [subst_input] at this
    -- the slot's interval starts at `1/32`
    have rQ' : RH v E (refineQ A) suQ := ⟨fun x' hx' => by
        obtain ⟨s', h1, h2, h3, h4⟩ := rQ.all x' hx'
        refine ⟨s', ?_, h2, h3, h4⟩
        simp only [refineQ]; push_cast
        exact max_le h1 (by rw [WgslReassoc.exact_RA v hx']; exact hqe),
      rQ.sflag, rQ.sdata, rQ.pflag, rQ.pdata, rQ.mflag, rQ.mdata⟩
    have hS : SlotsR v E [refineQ A] [suQ] :=
      ⟨rfl, fun j hv _ => by
        obtain rfl : j = 0 := by simp at hv; omega
        exact rQ'⟩
    have r := ev_robust 0 (suBody i) _ _ v E R (slotEnv_R henv hS) hR
    have e : WgslLets.subst (WgslLets.lookup [suQ]) (suBody i) = WgslScreen.spatialUnit suVec i := by
      rw [← su_lets]; rfl
    rw [e] at r
    exact fun x' hx' => (r.all x' hx').1

end BlackHole.WgslSafeDomains
