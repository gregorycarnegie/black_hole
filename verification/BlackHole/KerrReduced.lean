module
public import BlackHole.KerrArithmetic
public import BlackHole.ValidatedStep

/-! Keep the exactly conserved covariant time momentum as a parameter. This
avoids repeatedly inflating its initial uncertainty as a dynamical error. -/

@[expose] public section
noncomputable section
open Set
namespace BlackHole.KerrField

abbrev ReducedPhase := Cartesian.Space × Cartesian.Space × (Fin 4 → ℝ)

def liftPhase (pt : ℝ) (y : ReducedPhase) : Phase :=
  (y.1,Fin.cases pt y.2.1,y.2.2)

def dropPhase (y : Phase) : ReducedPhase :=
  (y.1,(fun i => y.2.1 i.succ),y.2.2)

def reducedRhs (mass : ℝ) (a : Cartesian.Space) (pt : ℝ) (y : ReducedPhase) : ReducedPhase :=
  dropPhase (phaseRhs mass a (liftPhase pt y))

theorem drop_lift (pt : ℝ) (y : ReducedPhase) : dropPhase (liftPhase pt y) = y := by
  rfl

/-- A solution of the ten-dimensional parameterized system is a solution of
all eleven original equations, including the stationary time momentum. -/
theorem lift_solution (mass : ℝ) (a : Cartesian.Space) (pt : ℝ)
    (curve : ℝ → ReducedPhase) (s : Set ℝ) (t : ℝ)
    (hcurve : HasDerivWithinAt curve (reducedRhs mass a pt (curve t)) s t) :
    HasDerivWithinAt (fun u => liftPhase pt (curve u))
      (phaseRhs mass a (liftPhase pt (curve t))) s t := by
  let R := reducedRhs mass a pt (curve t)
  have hx : HasDerivWithinAt (fun u => (curve u).1) R.1 s t := hcurve.fst
  have hpair : HasDerivWithinAt (fun u => (curve u).2) R.2 s t := hcurve.snd
  have hp3 : HasDerivWithinAt (fun u => (curve u).2.1) R.2.1 s t := hpair.fst
  have hf4 : HasDerivWithinAt (fun u => (curve u).2.2) R.2.2 s t := hpair.snd
  have hp : HasDerivWithinAt
      (fun u => fun i : Fin 4 => Fin.cases (motive := fun _ : Fin 4 => ℝ) pt (curve u).2.1 i)
      (fun i : Fin 4 => Fin.cases (motive := fun _ : Fin 4 => ℝ) 0
        (reducedRhs mass a pt (curve t)).2.1 i) s t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    cases i using Fin.cases with
    | zero => simpa only [Fin.cases_zero] using hasDerivWithinAt_const t s pt
    | succ i => simpa only [Fin.cases_succ] using (hasDerivWithinAt_pi.mp hp3) i
  have h := HasDerivWithinAt.prodMk hx (HasDerivWithinAt.prodMk hp hf4)
  have hR : (R.1,(fun i : Fin 4 => Fin.cases 0 R.2.1 i),R.2.2) =
      phaseRhs mass a (liftPhase pt (curve t)) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        cases i using Fin.cases with
        | zero => exact (phase_rhs_stationary mass a (liftPhase pt (curve t))).symm
        | succ i => rfl
      · rfl
  rw [hR] at h
  exact h

end BlackHole.KerrField
