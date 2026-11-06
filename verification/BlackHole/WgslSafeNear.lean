module

public import BlackHole.WgslDomain
public import BlackHole.WgslAddKerr

/-! Neighbourhoods of a Kerr configuration on which the `Safe` conditions of
`add_kerr`, `screen_frame` and `sample_plasma` hold (obligation F2).

The large kernels read a metric, its inverse and derivatives, a momentum and
a screen vector, which are not free: a domain of physical positions and rays
would compose these kernels with the metric's sensitivity (N2–N4), and naive
interval covers of it need millions of boxes. The theorems below prove
`Safe` on boxes around one consistent configuration: the Kerr–Schild metric
and inverse at `(8, 0.1, 0.5)` for mass `1` and spin `(0, 0.9, 0)`, a null
momentum and a transverse screen vector there, and typical disk and camera
parameters. They show the `Safe` hypotheses of these bounds are satisfiable
on open sets, so the bounds are not vacuous.

Each theorem evaluates `WgslDomain.ev` (slot by slot for the `let` programs)
on one box in the kernel and applies its soundness theorem. -/

@[expose] public section

namespace BlackHole.WgslSafeNear
open Wgsl WgslExpr GExpr WgslPlasma WgslDomain

/-- Inputs 0–55 of `sample_plasma` (and 0–39 of `screen_frame`), rounded to
denominators below `2²⁰`: metric 0–15, inverse 16–31, momentum 32–35,
screen 36–39, position 40–42, disk `r1 = 6`, `r2 = 20`, `h_thin = 0.05`,
`h_hot = 0.3`, `spin = 0.9`, `isco = 2.32`, `r_trunc = 10`, camera `230` GHz,
Faraday and conversion depths `0.5` and `0.25`, warp `r_bp = 15`, tilt `10°`,
twist `30°`. -/
def kerrRef : List ℚ :=
  [-583645/779316, 228177/922937, 2742/869903, 45339/1037650, 228177/922937, 824359/662968,
   2727/878621, 19618/455981, 2742/869903, 2727/878621, 935058/935021, 307/559672, 45339/1037650,
   19618/455981, 307/559672, 830993/824722, -974987/779316, 228177/922937, 2742/869903,
   45339/1037650, 228177/922937, 501577/662968, -2727/878621, -19618/455981, 2742/869903,
   -2727/878621, 934984/935021, -307/559672, 45339/1037650, -19618/455981, -307/559672,
   818451/824722, 125019/179015, -3/5, 0, -4/5, 0, 0, 1, 0, 8, 1/10, 1/2, 6, 20, 1/20, 3/10,
   9/10, 58/25, 10, 230, 1/2, 1/4, 15, 10, 30]

def minkowski : List ℚ := [-1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]

/-- Inputs 0–88 of `add_kerr` for one source on flat space at the same point:
position, spin, mass `1`, the Kerr radius `raw_r`, Minkowski metric and
inverse, zero derivatives, clearance `1000`. -/
def kerrSourceRef : List ℚ :=
  [8, 1/10, 1/2, 0, 9/10, 0, 1, 7005478/879471] ++ minkowski ++ minkowski ++
    List.replicate 48 0 ++ [1000]

set_option maxRecDepth 100000 in
theorem plasma_near_ok : (([0,1,2,3] : List (Fin 4)).all fun m =>
    evLetsAll 3 (nearEnv kerrRef (1/16384)) (plasmaLets m) ((List.finRange 12).map plasmaOut)) = true := by
  decide +kernel

/-- `sample_plasma` satisfies `Safe`, so its running bound holds, for all four
disk models and all twelve fields, at every input within `2⁻¹⁴ (1 + |ref|)`
of `kerrRef` with errors up to that. -/
theorem sample_plasma_safe_near (model : Fin 4) (o : Fin 12) (v E : ℕ → ℝ)
    (h : Near kerrRef (1/16384) v E) : (plasma model o).Safe v E := by
  have hm := List.all_eq_true.mp plasma_near_ok model (by fin_cases model <;> simp)
  exact evLetsAll_sound _ _ _ _ hm v E (nearEnv_H h) _
    (List.mem_map.mpr ⟨o, List.mem_finRange o, rfl⟩)

def frameOuts : List GExpr :=
  ([0,1,2] : List (Fin 3)).flatMap fun c => ([0,1,2] : List (Fin 3)).map fun i =>
    WgslLets.ref (WgslScreen.frameSlot c i)

set_option maxRecDepth 100000 in
theorem frame_near_ok :
    evLetsAll 0 (nearEnv (kerrRef.take 40) (1/1024)) WgslScreen.frameLets frameOuts = true := by
  decide +kernel

/-- `screen_frame` satisfies `Safe` for every input within
`2⁻¹⁰ (1 + |ref|)` of the first 40 entries of `kerrRef`, errors up to that. -/
theorem screen_frame_safe_near (col i : Fin 3) (v E : ℕ → ℝ)
    (h : Near (kerrRef.take 40) (1/1024) v E) : (WgslScreen.frame col i).Safe v E :=
  evLetsAll_sound _ _ _ _ frame_near_ok v E (nearEnv_H h) _
    (by fin_cases col <;> fin_cases i <;> simp [frameOuts])

def kerrOuts : List WgslAddKerr.Output :=
  (List.finRange 4).flatMap (fun i => (List.finRange 4).flatMap fun j => [.metric i j, .inverse i j]) ++
  (List.finRange 3).flatMap (fun e => (List.finRange 4).flatMap fun i =>
    (List.finRange 4).map fun j => .derivative e i j) ++ [.clearance]

set_option maxRecDepth 100000 in
theorem kerr_near_ok : (kerrOuts.all fun o =>
    (ev 0 (nearEnv kerrSourceRef (1/128)) (WgslAddKerr.program o)).isSome) = true := by
  decide +kernel

/-- Every `add_kerr` output (metric, inverse with its excision test,
derivatives, clearance) satisfies `Safe` for every input within
`2⁻⁷ (1 + |ref|)` of `kerrSourceRef`, errors up to that. -/
theorem add_kerr_safe_near (o : WgslAddKerr.Output) (v E : ℕ → ℝ)
    (h : Near kerrSourceRef (1/128) v E) : (WgslAddKerr.program o).Safe v E := by
  have ho : o ∈ kerrOuts := by
    cases o <;> simp [kerrOuts, List.mem_flatMap, List.mem_finRange]
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp kerr_near_ok o ho)
  exact (ev_sound 0 _ _ v E R (nearEnv_H h) hR).2

end BlackHole.WgslSafeNear
