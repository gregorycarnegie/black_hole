module

public import BlackHole.KernelFixture
public import BlackHole.PlasmaEmission
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The CUDA renderer contracts metric derivatives with vectors before
combining them. This keeps the exact geodesic equation and the existing
3e-4 arithmetic error limit, while avoiding two temporary matrices. -/

@[expose] public section
noncomputable section

namespace BlackHole.CudaGeodesic
open WgslPoly PExpr WgslGeodesic

def contractedProduct (a b : Fin 4 → PExpr) (i : Fin 4) : PExpr :=
  sum3 fun e => mul (a e.succ) (mv (dmat e) b i)

def screenRhs (i : Fin 4) : PExpr :=
  mul (const (-1/2)) (mv inv
    (fun j => sub (add (contractedProduct k f j) (contractedProduct f k j)) (contracted j)) i)

def rhs (o : Fin 11) : PExpr :=
  if h : o.val < 3 then posRhs ⟨o,h⟩ else if h' : o.val < 7 then momRhs ⟨o-3,by omega⟩
  else screenRhs ⟨o-7,by omega⟩

set_option maxHeartbeats 2000000 in
theorem rhs_exact_eq (v : ℕ → ℝ) (o : Fin 11) :
    (rhs o).exact v = (WgslGeodesic.rhs o).exact v := by
  fin_cases o <;>
    simp [rhs, screenRhs, contractedProduct, WgslGeodesic.rhs, WgslGeodesic.screenRhs,
      posRhs, momRhs, contracted, comb, mv, dot, sum3, sum4, PExpr.exact] <;> ring

theorem rhs_divcOk (o : Fin 11) : (rhs o).DivcOk := by
  have hin (n : ℕ) : (input n).DivcOk := trivial
  have hk (i : Fin 4) : (k i).DivcOk := divcOk_mv (fun _ _ => hin _) (fun _ => hin _) i
  have hprod (a b : Fin 4 → PExpr) (ha : ∀ i, (a i).DivcOk)
      (hb : ∀ i, (b i).DivcOk) (j : Fin 4) : (contractedProduct a b j).DivcOk :=
    divcOk_sum3 fun e => ⟨ha e.succ, divcOk_mv (fun _ _ => hin _) hb j⟩
  have hcon (i : Fin 4) : (contracted i).DivcOk := by
    cases i using Fin.cases with
    | zero => trivial
    | succ e => exact divcOk_dot hk (divcOk_mv (fun _ _ => hin _) (fun _ => hin _))
  unfold rhs
  split_ifs
  · exact hk _
  · refine ⟨trivial, ?_⟩
    generalize (⟨o-3, _⟩ : Fin 4) = i
    cases i using Fin.cases with
    | zero => trivial
    | succ e => exact divcOk_dot hk (divcOk_mv (fun _ _ => hin _) hk)
  · have hj (j : Fin 4) :
        (sub (add (contractedProduct k f j) (contractedProduct f k j)) (contracted j)).DivcOk :=
        ⟨⟨hprod k f hk (fun _ => hin _) j, hprod f k (fun _ => hin _) hk j⟩, hcon j⟩
    exact ⟨trivial, divcOk_mv (M := inv) (fun _ _ => hin _) hj _⟩

theorem rhs_ops (o : Fin 11) : (rhs o).ops (fun _ => 0) ≤ 872 := by
  fin_cases o <;> decide

theorem geodesic_rhs_exact_inputs (v : ℕ → ℝ) (o : Fin 11) (y : ℝ)
    (hy : (rhs o).Computes v y) :
    |y-(WgslGeodesic.rhs o).exact v| ≤ 3/10000*(rhs o).absEval (fun i => |v i|) := by
  have hall := error v v (fun i => |v i|) (fun _ => 0) (fun _ => le_rfl)
    (fun i => by simp [Γ]) (rhs o) y (rhs_divcOk o) hy
  have hA : 0 ≤ (rhs o).absEval (fun i => |v i|) := (abs_nonneg _).trans hall.1
  rw [← rhs_exact_eq v o]
  exact hall.2.trans (mul_le_mul_of_nonneg_right
    ((Γ_mono (rhs_ops o)).trans Γ872_small.le) hA)

/-- The intensity-only thermal branch has no synchrotron contribution. -/
theorem thermal_intensity (model : ℕ) (hmodel : model ≠ 1)
    (argument temperature ratio perpendicular frequency energy : ℝ) (i : Fin 3) :
    Plasma.thermalColor model argument temperature i +
      Plasma.synchrotronColor model argument ratio perpendicular frequency energy i =
      Plasma.blackbodyColor temperature i := by
  simp [Plasma.thermalColor, Plasma.synchrotronColor, Plasma.hotWeight, hmodel]

theorem orbital_power (r : ℝ) (hr : 0 < r) : r ^ (3/2 : ℝ) = r * Real.sqrt r := by
  rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hr, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem conversion_power (frequency : ℝ) :
    frequency ^ (3 : ℝ) = frequency * frequency * frequency := by
  rw [Real.rpow_ofNat]
  ring

/-- The shared reciprocals leave the exact metric derivatives unchanged. -/
theorem metric_derivative_reciprocals (h r dr ax a denominator : ℝ) :
    h * (3 * dr / r - (4 * r * (r*r) * dr + 2 * ax * a) / denominator) =
      h * (3 * dr * (1/r) - (4 * r * (r*r) * dr + 2 * ax * a) * (1/denominator)) := by
  simp only [div_eq_mul_inv, one_mul]

def kernels : List (String × PExpr) :=
  (List.finRange 11).map fun o => ("geodesic_rhs", rhs o)

def render : String := String.intercalate "\n"
  (kernels.map fun (name, expression) => name ++ " " ++ KernelFixture.sexp expression) ++ "\n"

private meta def fixtureText : String := include_str "../fixtures/cuda-geodesic.sexp"

macro "cuda_geodesic_fixture" : term => KernelFixture.parseFixture fixtureText

def fixture : List (String × PExpr) := cuda_geodesic_fixture

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The GPU test reads exactly the expression whose bound is proved above. -/
theorem fixture_eq : fixture = kernels := by
  decide +kernel

end BlackHole.CudaGeodesic
