module
public import BlackHole.KerrSmoothness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The arithmetic RHS used by the interval evaluator, connected to the
Hamiltonian/parallel-screen field already used by the Kerr proofs. -/

@[expose] public section
noncomputable section
open Matrix
namespace BlackHole.KerrField

def screenCovector (dg : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (k f : Fin 4 → ℝ) (d : Fin 4) : ℝ :=
  (∑ b, k b*(dg b).mulVec f d)+(∑ c, f c*(dg c).mulVec k d)-
    dotProduct k ((dg d).mulVec f)

set_option maxHeartbeats 1000000 in
theorem screen_rhs_arithmetic (inv : Matrix (Fin 4) (Fin 4) ℝ)
    (dg : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (k f : Fin 4 → ℝ) (i : Fin 4) :
    -(∑ c, Transport.contractedConnection inv dg k i c*f c) =
      -(1/2:ℝ)*inv.mulVec (screenCovector dg k f) i := by
  simp only [Transport.contractedConnection,Transport.loweredConnection,screenCovector,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

def arithmeticRhs (mass : ℝ) (a : Cartesian.Space) (state : Phase) : Phase :=
  let inv := explicitInverse mass a state.1
  let dg := metricD mass a state.1
  let k := inv.mulVec state.2.1
  ((fun i => k i.succ), Transport.momentumForce dg k,
    fun i => -(1/2:ℝ)*inv.mulVec (screenCovector dg k state.2.2) i)

theorem arithmetic_rhs_eq (mass : ℝ) (a : Cartesian.Space) (state : Phase)
    (hr : 0 < Cartesian.radius a state.1) : arithmeticRhs mass a state = phaseRhs mass a state := by
  dsimp only [arithmeticRhs,phaseRhs]
  rw [inverse_eq_explicit mass a state.1 hr]
  congr 2
  funext i
  exact (screen_rhs_arithmetic _ _ _ _ i).symm

theorem phase_rhs_stationary (mass : ℝ) (a : Cartesian.Space) (state : Phase) :
    (phaseRhs mass a state).2.1 0 = 0 := by
  simp [phaseRhs,Transport.momentumForce,metricD]

end BlackHole.KerrField
