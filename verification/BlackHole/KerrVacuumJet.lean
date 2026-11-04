module
public import BlackHole.KerrRankDerivative
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet
open Cartesian (Space)

@[simp] theorem cases1 {B : Type*} (z : B) (f : Fin 3 → B) : Fin.cases z f (1 : Fin 4) = f 0 := rfl
@[simp] theorem cases2 {B : Type*} (z : B) (f : Fin 3 → B) : Fin.cases z f (2 : Fin 4) = f 1 := rfl
@[simp] theorem cases3 {B : Type*} (z : B) (f : Fin 3 → B) : Fin.cases z f (3 : Fin 4) = f 2 := rfl

def twist (l v : Space) : Space := crossProduct l v
def radiusD (l v : Space) : Space := l+twist l v
def cosineD (l v : Space) : Space := crossProduct l (twist l v)
def ellD (S r c : ℝ) (l : Space) (e i : Fin 3) : ℝ :=
  (r*(Cartesian.basis e i-l i*l e)-c*crossProduct l (Cartesian.basis e) i)/S
def ellDD (S r c : ℝ) (l v : Space) (f e i : Fin 3) : ℝ :=
  (radiusD l v f*(Cartesian.basis e i-l i*l e)-r*(ellD S r c l f i*l e+l i*ellD S r c l f e)-
    cosineD l v f*crossProduct l (Cartesian.basis e) i-
    c*crossProduct (ellD S r c l f) (Cartesian.basis e) i-
    ellD S r c l e i*(2*r*radiusD l v f+2*c*cosineD l v f))/S
def rDD (S r c : ℝ) (l v : Space) (e f : Fin 3) : ℝ :=
  (r*(Cartesian.basis e f-radiusD l v e*radiusD l v f+cosineD l v e*cosineD l v f)-
    c*(radiusD l v e*cosineD l v f+cosineD l v e*radiusD l v f))/S
def cDD (S r c : ℝ) (l v : Space) (e f : Fin 3) : ℝ :=
  (-r*(radiusD l v e*cosineD l v f+cosineD l v e*radiusD l v f)-
    c*(Cartesian.basis e f-radiusD l v e*radiusD l v f+cosineD l v e*cosineD l v f))/S
def H (S r m : ℝ) : ℝ := m*r/S
def HD (S r c m : ℝ) (l v : Space) (e : Fin 3) : ℝ :=
  m*(c^2-r^2)/S^2*radiusD l v e-2*m*r*c/S^2*cosineD l v e
def HDD (S r c m : ℝ) (l v : Space) (e f : Fin 3) : ℝ :=
  2*m*r*(r^2-3*c^2)/S^3*radiusD l v e*radiusD l v f+
    2*m*c*(3*r^2-c^2)/S^3*(radiusD l v e*cosineD l v f+cosineD l v e*radiusD l v f)-
    2*m*r*(r^2-3*c^2)/S^3*cosineD l v e*cosineD l v f+
    m*(c^2-r^2)/S^2*rDD S r c l v e f-2*m*r*c/S^2*cDD S r c l v e f
def ell4 (l : Space) : Fin 4 → ℝ := Fin.cases 1 l
def raised (l : Space) : Fin 4 → ℝ := Fin.cases (-1) l
def dell4 (S r c : ℝ) (l : Space) (e : Fin 4) : Fin 4 → ℝ :=
  Fin.cases 0 (fun f => Fin.cases 0 (ellD S r c l f)) e
def ddell4 (S r c : ℝ) (l v : Space) (e f : Fin 4) : Fin 4 → ℝ :=
  Fin.cases 0 (fun i => Fin.cases 0 (fun j => Fin.cases 0 (ellDD S r c l v i j)) f) e
def h4 (S r c m : ℝ) (l v : Space) : Fin 4 → ℝ := Fin.cases 0 (HD S r c m l v)
def hh4 (S r c m : ℝ) (l v : Space) (e : Fin 4) : Fin 4 → ℝ :=
  Fin.cases 0 (fun i => Fin.cases 0 (HDD S r c m l v i)) e
def inv (S r m : ℝ) (l : Space) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j => Cartesian.eta i j-2*H S r m*raised l i*raised l j)
def dg (S r c m : ℝ) (l v : Space) (e : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j => 2*h4 S r c m l v e*ell4 l i*ell4 l j+
    2*H S r m*(dell4 S r c l e i*ell4 l j+ell4 l i*dell4 S r c l e j))
def ddg (S r c m : ℝ) (l v : Space) (e f : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j => 2*hh4 S r c m l v e f*ell4 l i*ell4 l j+
    2*h4 S r c m l v e*(dell4 S r c l f i*ell4 l j+ell4 l i*dell4 S r c l f j)+
    2*h4 S r c m l v f*(dell4 S r c l e i*ell4 l j+ell4 l i*dell4 S r c l e j)+
    2*H S r m*(ddell4 S r c l v e f i*ell4 l j+dell4 S r c l f i*dell4 S r c l e j+
      dell4 S r c l e i*dell4 S r c l f j+ell4 l i*ddell4 S r c l v e f j))

def di (S r c m : ℝ) (l v : Space) (e : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  -KerrField.rankDerivative (2*H S r m) (2*h4 S r c m l v e)
    (raised l) (fun i => KerrField.signature i*dell4 S r c l e i)

theorem inverseD_closed (S r c m : ℝ) (l v : Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (e a b : Fin 4) :
    Curvature.inverseD (inv S r m l) (dg S r c m l v) e a b = di S r c m l v e a b := by
  have hu : dotProduct (ell4 l) (fun i => KerrField.signature i*ell4 l i) = 0 := by
    simp [dotProduct, Fin.sum_univ_succ, ell4, KerrField.signature]
    nlinarith [hunit]
  have ho : dotProduct (dell4 S r c l e) (fun i => KerrField.signature i*ell4 l i) = 0 := by
    cases e using Fin.cases with
    | zero => simp [dell4, dotProduct]
    | succ e =>
      change dotProduct (Fin.cases 0 (ellD S r c l e)) (fun i => KerrField.signature i*ell4 l i) = 0
      simp only [dotProduct, Fin.sum_univ_succ, ell4, Fin.cases_zero, Fin.cases_succ,
        KerrField.signature, Fin.succ_ne_zero, ite_true, ite_false, zero_mul, mul_one, one_mul,
        zero_add]
      fin_cases e <;> simp [ellD, Cartesian.basis, cross_apply]
      all_goals field_simp; grobner
  have hinv : inv S r m l = KerrField.rankInverse (2*H S r m) (ell4 l) := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [inv, KerrField.rankInverse, KerrField.minkowski, Matrix.vecMulVec_apply,
        Matrix.diagonal_apply, KerrField.signature, Cartesian.eta, ell4, raised,
        Fin.succ_ne_zero, eq_comm]
    ring
  have hdg : dg S r c m l v e =
      KerrField.rankDerivative (2*H S r m) (2*h4 S r c m l v e) (ell4 l) (dell4 S r c l e) := by
    ext i j
    simp [dg, KerrField.rankDerivative, Matrix.vecMulVec_apply]
    ring
  have hprod : (∑ i, ∑ j, inv S r m l a i*dg S r c m l v e i j*inv S r m l j b) =
      (inv S r m l*dg S r c m l v e*inv S r m l) a b := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hr := KerrField.rank_inverse_derivative (2*H S r m) (2*h4 S r c m l v e)
    (ell4 l) (dell4 S r c l e) hu ho
  unfold Curvature.inverseD
  rw [hprod, hinv, hdg]
  have hv : (fun i => KerrField.signature i*ell4 l i) = raised l := by
    ext i
    cases i using Fin.cases <;> simp [KerrField.signature, ell4, raised]
  change (-(KerrField.rankInverse _ _*KerrField.rankDerivative _ _ _ _*KerrField.rankInverse _ _)) a b = _
  rw [hr, hv]
  rfl

end BlackHole.KerrVacuumJet
