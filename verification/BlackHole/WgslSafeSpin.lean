module

public import BlackHole.WgslSafeBoxes

/-! A closed-form domain on which every reassociation of `add_kerr`'s spin
scaling satisfies `Safe` (obligation F2), covered by boxes (`WgslSafeBoxes`). -/

@[expose] public section

namespace BlackHole.WgslSafeDomains
open Wgsl WgslExpr GExpr WgslPlasma WgslDomain

/-! ### `spin_scale` -/

/-- Spin in octave `k` and slab `s` with errors up to `2⁻²⁰` of `2^(k+1)`;
any mass and mass error up to `2⁶⁴`. -/
def spinEnv (k : ℤ) (s : ℕ) : ℕ → Option Av := fun i =>
  if i < 3 then some (slabAv k s i (2*pow2 k/1048576))
  else if i = 3 then some (Av.mk3 (-18446744073709551616) 18446744073709551616 18446744073709551616)
  else none

/-- The spin scaling with its divisor as a `let` slot. -/
def spinD : GExpr :=
  max (WgslAddKerr.c 1) (div WgslAddKerr.spinNorm (WgslAddKerr.c WgslAddKerr.f32_0_999))
def spinOut (j : Fin 3) : GExpr := div (mul (input 3) (input j)) (WgslLets.ref 0)

lemma spin_lets (j : Fin 3) : WgslLets.withLets [spinD] (spinOut j) = WgslAddKerr.spinScale j := by
  fin_cases j <;> rfl

set_option maxRecDepth 100000 in
theorem spinEnv_ok : ((List.range 41).all fun k => (List.range 6).all fun s =>
    evLetsAll 0 (spinEnv ((k:ℤ)-20) s) [spinD] (([0,1,2] : List (Fin 3)).map spinOut)) = true := by
  decide +kernel

/-- Every reassociation of `add_kerr`'s spin scaling
`mass*spin/max(1, length(spin)/0.999)` satisfies `Safe` for every spin with `2⁻²⁰ ≤ max |spinᵢ| ≤ 2²⁰` and component errors up
to `2⁻²⁰ max |spinᵢ|`, and every mass and mass error up to `2⁶⁴`. A zero spin
is excluded: WGSL leaves `sqrt(0) = 1/inverseSqrt(0)` unspecified. -/
theorem spin_scale_safe (j : Fin 3) (v E : ℕ → ℝ) (h1 : (2:ℝ)^(-20:ℤ) ≤ vmax v 0)
    (h2 : vmax v 0 ≤ (2:ℝ)^(20:ℤ)) (hE : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ vmax v 0/2^20)
    (hm : |v 3| ≤ 2^64) (hEm : 0 ≤ E 3 ∧ E 3 ≤ 2^64) :
    ∀ x', WgslReassoc.RA (WgslAddKerr.spinScale j) x' → x'.Safe v E := by
  obtain ⟨k, s, kl, kh, hs, hsl, hb⟩ := vec_cover v 0 h1 h2
  have hj := all_range (all_range spinEnv_ok (k := (k+20).toNat) (by omega)) hs
  rw [show (((k+20).toNat : ℕ) : ℤ)-20 = k by omega] at hj
  rw [← spin_lets]
  refine evLetsAll_robust _ _ _ _ hj v E ?_ _ (List.mem_map.mpr ⟨j, by fin_cases j <;> simp, rfl⟩)
  intro i A hA
  unfold spinEnv at hA
  split_ifs at hA with p q <;> simp only [Option.some.injEq] at hA <;> subst hA
  · obtain ⟨hx, hv⟩ := hb i p
    obtain ⟨e0, e1⟩ := hE i p
    refine slabAv_H (by simpa using hx) (fun e => by simpa using (hsl i p).1 e)
      (fun e => by simpa using (hsl i p).2 e) e0 (e1.trans ?_)
    push_cast; rw [pow2_eq]; linarith
  · subst q
    have := abs_le.mp hm
    exact ⟨by push_cast; linarith, by push_cast; linarith, hEm.1, by push_cast; linarith⟩

end BlackHole.WgslSafeDomains
