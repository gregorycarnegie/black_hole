module

public import BlackHole.KerrJetBridge
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace BlackHole.KerrVacuumJet

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem connection_trace_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0) (b : Fin 4) :
    (∑ a, Curvature.christoffel (inv S r m l) (dg S r c m l v) a a b) = 0 := by
  fin_cases b <;> simp only [Curvature.christoffel, Fin.sum_univ_succ]
  all_goals simp only [inv, dg, Matrix.of_apply]
  all_goals simp [KerrField.signature, Cartesian.eta, h4, dell4, ell4, raised]
  all_goals simp [H, HD, ellD, radiusD, cosineD, twist, cross_apply, Cartesian.basis]
  all_goals field_simp; grobner (ringSteps := 200000)

end BlackHole.KerrVacuumJet

namespace BlackHole.KerrField

theorem connection_trace_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (b : Fin 4) : (∑ d, connection mass a x d d b) = 0 := by
  have hu := spatialEll_unit a x hr
  simp [dotProduct, Fin.sum_univ_succ] at hu
  have hunit : Cartesian.spatialEll a x 0^2+Cartesian.spatialEll a x 1^2+
      Cartesian.spatialEll a x 2^2 = 1 := by nlinarith
  simp only [connection, inverse_eq_optical_jet mass a x hr, metricD_eq_optical_jet mass a x hr]
  exact KerrVacuumJet.connection_trace_zero _ _ _ _ _ _ hunit
    (ne_of_gt (Cartesian.sigma_positive a x hr)) b

theorem connectionD_trace_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (e b : Fin 4) :
    (∑ d, Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x)
      (metricDD mass a x) e d d b) = 0 := by
  obtain ⟨hdisc,hroot⟩ := Cartesian.positive_radius_domain a x hr
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun d _ =>
    connection_derivative mass a x e d d b hdisc hroot (metric_nonsingular mass a x hr))
  have hrad : ContinuousAt (fun t => Cartesian.radius a (Schwarzschild.line4 x e t)) 0 := by
    cases e using Fin.cases with
    | zero => exact continuousAt_const
    | succ e => exact (Cartesian.radius_derivative a x e hdisc hroot).continuousAt
  have hevent : ∀ᶠ t in nhds (0 : ℝ), 0 < Cartesian.radius a (Schwarzschild.line4 x e t) :=
    hrad.eventually (lt_mem_nhds (by simpa only [Schwarzschild.line4_zero] using hr))
  have heq : (fun t => ∑ d, connection mass a (Schwarzschild.line4 x e t) d d b) =ᶠ[nhds (0 : ℝ)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hevent] with t ht
    exact connection_trace_zero mass a _ ht b
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq)

theorem connection_lower_symmetric (mass : ℝ) (a x : Cartesian.Space) (i b c : Fin 4) :
    connection mass a x i b c = connection mass a x i c b := by
  unfold connection Curvature.christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [metricD_symmetric mass a x d b c]
  ring

theorem connectionD_lower_symmetric (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (e i b c : Fin 4) :
    Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x) e i b c =
      Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x) e i c b := by
  obtain ⟨hdisc,hroot⟩ := Cartesian.positive_radius_domain a x hr
  have hleft := connection_derivative mass a x e i b c hdisc hroot (metric_nonsingular mass a x hr)
  have hright := connection_derivative mass a x e i c b hdisc hroot (metric_nonsingular mass a x hr)
  have heq : (fun t => connection mass a (Schwarzschild.line4 x e t) i b c) =
      (fun t => connection mass a (Schwarzschild.line4 x e t) i c b) :=
    funext (fun t => connection_lower_symmetric mass a _ i b c)
  rw [heq] at hleft
  exact hleft.unique hright

theorem ricci_reduced (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (b c : Fin 4) :
    ricci mass a x b c =
      (∑ d, Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x) d d b c)-
        ∑ d, ∑ e, connection mass a x d c e*connection mass a x e b d := by
  let G := connection mass a x
  let D := Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x)
  have hd : (∑ d, D c d b d) = 0 := by
    calc
      _ = ∑ d, D c d d b := by
        apply Finset.sum_congr rfl
        intro d _
        exact connectionD_lower_symmetric mass a x hr c d b d
      _ = 0 := connectionD_trace_zero mass a x hr c b
  have hg : (∑ d, ∑ e, G d d e*G e b c) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, G, connection_trace_zero mass a x hr, zero_mul, Finset.sum_const_zero]
  change (∑ d, (D d d b c-D c d b d+∑ e, (G d d e*G e b c-G d c e*G e b d))) = _
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hd, hg]
  ring

theorem ricci_symmetric (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (b c : Fin 4) : ricci mass a x b c = ricci mass a x c b := by
  rw [ricci_reduced mass a x hr b c, ricci_reduced mass a x hr c b]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    exact connectionD_lower_symmetric mass a x hr d d b c
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    ring

end BlackHole.KerrField
