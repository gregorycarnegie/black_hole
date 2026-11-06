module

public import BlackHole.WgslSafeBoxes

/-! A closed-form domain on which every reassociation of `polarization_color`'s
hue view satisfies `Safe` (obligation F2), covered by boxes (`WgslSafeBoxes`). -/

@[expose] public section

namespace BlackHole.WgslSafeDomains
open Wgsl WgslExpr GExpr WgslPlasma WgslDomain

/-! ### `polarization_color` -/

/-- Octave `k` of the intensity `I`; slab `s` puts `Q` (`s = 0, 1`) or `U`
(`s = 2, 3`) at least `7/640` of `2^k` away from zero, positive or negative. -/
def polBox (k : ℤ) (s : ℕ) : ℕ → Option Av :=
  let a := pow2 k
  let e := 2*a/1048576
  let wide : Av := Av.mk3 (-2*a) (2*a) e
  let pos : Av := Av.mk3 (7/640*a) (2*a) e
  let neg : Av := Av.mk3 (-2*a) (-(7/640*a)) e
  fun i => match i with
    | 0 => some (Av.mk3 a (2*a) e)
    | 1 => some (if s = 0 then pos else if s = 1 then neg else wide)
    | 2 => some (if s = 2 then pos else if s = 3 then neg else wide)
    | _ => none

/-- `polarization_color`'s hue view with its shared values as `let` slots:
`pol.x` 0, `pol.y` 1, `rho2` 2, `rho` 3, `ux` 4, `uy` 5. -/
def polSlots : List GExpr :=
  let pol (i : ℕ) : GExpr := clamp (div (input (i+1)) (input 0)) (c (-1)) (c 1)
  [pol 0, pol 1, add (mul (WgslLets.ref 0) (WgslLets.ref 0)) (mul (WgslLets.ref 1) (WgslLets.ref 1)),
    sqrt (WgslLets.ref 2), div (WgslLets.ref 0) (WgslLets.ref 3), div (WgslLets.ref 1) (WgslLets.ref 3)]

def polOut (k : Fin 3) : GExpr :=
  let ux := WgslLets.ref 4
  let uy := WgslLets.ref 5
  let comp : Fin 3 → GExpr := ![ux, add (mul (c (-1/2)) ux) (mul (c LSQRT3_2) uy),
    sub (mul (c (-1/2)) ux) (mul (c LSQRT3_2) uy)]
  lt (neg (input 0)) (-L1em8)
    (lt (neg (WgslLets.ref 2)) 0 (mul (add (c (1/2)) (mul (c (1/2)) (comp k)))
      (clamp (WgslLets.ref 3) (c 0) (c 1))) (c 0)) (c 0)

lemma pol_lets (k : Fin 3) : WgslLets.withLets polSlots (polOut k) = polarizationHue k := by
  fin_cases k <;> rfl

set_option maxRecDepth 100000 in
theorem polBox_ok : ((List.range 53).all fun k => (List.range 4).all fun s =>
    evLetsAll 0 (polBox ((k:ℤ)-26) s) polSlots (([0,1,2] : List (Fin 3)).map polOut)) = true := by
  decide +kernel

/-- Every reassociation of `polarization_color`'s hue view (`WgslReassoc.RA`)
satisfies `Safe`, so its running bound holds, for every intensity in
`[2⁻²⁶, 2²⁶]` (above the `10⁻⁸` cutoff), every `|Q|, |U| ≤ I` with linear
polarization fraction at least `1/64`, and input errors up to `2⁻²⁰ I`. -/
theorem polarization_safe (j : Fin 3) (v E : ℕ → ℝ) (hI : (2:ℝ)^(-26:ℤ) ≤ v 0)
    (hI' : v 0 ≤ (2:ℝ)^(26:ℤ)) (hQ : |v 1| ≤ v 0) (hU : |v 2| ≤ v 0)
    (hpol : (v 0/64)^2 ≤ v 1^2+v 2^2) (hE : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ v 0/2^20) :
    ∀ x', WgslReassoc.RA (polarizationHue j) x' → x'.Safe v E := by
  have hI0 : 0 < v 0 := lt_of_lt_of_le (by positivity) hI
  obtain ⟨k, hk1, hk2⟩ := octave hI0
  obtain ⟨kl, kh⟩ := octave_range hk1 hk2 hI hI'
  set a : ℝ := (2:ℝ)^k with ha
  have ha0 : 0 < a := by positivity
  have h2a : v 0 < 2*a := by rw [zpow_add_one₀ (by norm_num)] at hk2; rw [ha]; linarith
  have hslab : 7/640*a ≤ |v 1| ∨ 7/640*a ≤ |v 2| := by
    by_contra h
    simp only [not_or, not_le] at h
    have h1 : v 1^2 < (7/640*a)^2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h.1 (abs_nonneg _) (by norm_num)
    have h2 : v 2^2 < (7/640*a)^2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h.2 (abs_nonneg _) (by norm_num)
    have h3 : (a/64)^2 ≤ (v 0/64)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  obtain ⟨s, hs, hsl⟩ : ∃ s < 4, (s = 0 → 7/640*a ≤ v 1) ∧ (s = 1 → v 1 ≤ -(7/640*a)) ∧
      (s = 2 → 7/640*a ≤ v 2) ∧ (s = 3 → v 2 ≤ -(7/640*a)) := by
    rcases hslab with h | h
    · rcases le_total 0 (v 1) with h0 | h0
      · exact ⟨0, by norm_num, by simp; rwa [abs_of_nonneg h0] at h⟩
      · exact ⟨1, by norm_num, by simp; rw [abs_of_nonpos h0] at h; linarith⟩
    · rcases le_total 0 (v 2) with h0 | h0
      · exact ⟨2, by norm_num, by simp; rwa [abs_of_nonneg h0] at h⟩
      · exact ⟨3, by norm_num, by simp; rw [abs_of_nonpos h0] at h; linarith⟩
  have hok := all_range polBox_ok (k := (k+26).toNat) (by omega)
  have hj := all_range hok hs
  rw [show (((k+26).toNat : ℕ) : ℤ)-26 = k by omega] at hj
  rw [← pol_lets]
  refine evLetsAll_robust _ _ _ _ hj v E ?_ _ (List.mem_map.mpr ⟨j, by fin_cases j <;> simp, rfl⟩)
  have hpa : ((pow2 k : ℚ) : ℝ) = a := pow2_eq k
  have hb : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ ((2*pow2 k/1048576 : ℚ) : ℝ) := by
    intro i hi
    obtain ⟨e0, e1⟩ := hE i hi
    refine ⟨e0, e1.trans ?_⟩
    push_cast; rw [hpa]; linarith
  have q1 : -(2*a) ≤ v 1 ∧ v 1 ≤ 2*a := by
    have := abs_le.mp hQ; constructor <;> linarith
  have q2 : -(2*a) ≤ v 2 ∧ v 2 ≤ 2*a := by
    have := abs_le.mp hU; constructor <;> linarith
  intro i A hA
  match i with
  | 0 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    exact ⟨by push_cast; rw [hpa]; exact hk1, by push_cast; rw [hpa]; exact h2a.le,
      (hb 0 (by norm_num)).1, (hb 0 (by norm_num)).2⟩
  | 1 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    refine ⟨?_,?_,(hb 1 (by norm_num)).1,?_⟩
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · exact hsl.1 p
      · linarith
      · linarith
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · linarith
      · exact hsl.2.1 q
      · linarith
    · split_ifs <;> exact (hb 1 (by norm_num)).2
  | 2 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    refine ⟨?_,?_,(hb 2 (by norm_num)).1,?_⟩
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · exact hsl.2.2.1 p
      · linarith
      · linarith
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · linarith
      · exact hsl.2.2.2 q
      · linarith
    · split_ifs <;> exact (hb 2 (by norm_num)).2
  | n+3 => simp [polBox] at hA

/-- On the domain of `polarization_safe`, a WGSL evaluation of
`polarization_color`'s hue view in any association `x'` of its sums is within
the running bound of that association. -/
theorem polarization_error_all (j : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i)
    (hI : (2:ℝ)^(-26:ℤ) ≤ v 0) (hI' : v 0 ≤ (2:ℝ)^(26:ℤ)) (hQ : |v 1| ≤ v 0) (hU : |v 2| ≤ v 0)
    (hpol : (v 0/64)^2 ≤ v 1^2+v 2^2) (hE : ∀ i, i < 3 → E i ≤ v 0/2^20) (x' : GExpr)
    (hx' : WgslReassoc.RA (polarizationHue j) x') (y : ℝ) (hy : x'.Computes w y) :
    |y-(polarizationHue j).exact v| ≤ x'.bound v E := by
  rw [← WgslReassoc.exact_RA v hx']
  exact error x' v w E hw y (polarization_safe j v E hI hI' hQ hU hpol
    (fun i hi => ⟨(abs_nonneg _).trans (hw i), hE i hi⟩) x' hx') hy

end BlackHole.WgslSafeDomains
