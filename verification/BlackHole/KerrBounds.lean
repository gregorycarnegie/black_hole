module

public import BlackHole.CameraFrame

@[expose] public section
noncomputable section
namespace BlackHole.KerrField

theorem potential_le_mass_over_radius (mass : ℝ) (a x : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) :
    Cartesian.potential mass a x ≤ mass/Cartesian.radius a x := by
  let r := Cartesian.radius a x
  let b := Cartesian.b a x
  change mass*r^3/(r^4+b^2) ≤ mass/r
  calc
    _ ≤ mass*r^3/r^4 := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_add_of_nonneg_right (sq_nonneg b))
    _ = mass/r := by field_simp

theorem unit_mass_potential_bounds (a x : Cartesian.Space) (hr : 1 ≤ Cartesian.radius a x) :
    0 ≤ Cartesian.potential 1 a x ∧ Cartesian.potential 1 a x ≤ 1 := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  refine ⟨potential_nonnegative 1 a x (by norm_num) hr0,?_⟩
  exact le_trans (potential_le_mass_over_radius 1 a x (by norm_num) hr0)
    ((div_le_one hr0).mpr hr)

theorem ell_component_abs_le_one (a x : Cartesian.Space) (hr : 0 < Cartesian.radius a x)
    (i : Fin 4) : |Cartesian.ell a x i| ≤ 1 := by
  cases i using Fin.cases with
  | zero => simp [Cartesian.ell]
  | succ i =>
    have hu := spatialEll_unit a x hr
    have hi : (Cartesian.spatialEll a x i)^2 ≤ 1 := by
      calc
        _ ≤ ∑ j : Fin 3, (Cartesian.spatialEll a x j)^2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (Cartesian.spatialEll a x j)) (Finset.mem_univ i)
        _ = 1 := by
          simp only [dotProduct,← pow_two] at hu
          linarith
    simp only [Cartesian.ell,Fin.cases_succ]
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

theorem raisedEll_component_abs_le_one (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i : Fin 4) : |raisedEll a x i| ≤ 1 := by
  have hi := ell_component_abs_le_one a x hr i
  by_cases h : i = 0 <;> simpa [raisedEll,signature,h] using hi

private theorem rank_entry_bound (eta H u v : ℝ) (he : |eta| ≤ 1)
    (hH : 0 ≤ H) (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |eta+2*H*u*v| ≤ 1+2*H := by
  have hprod : |u| * |v| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hu hv (abs_nonneg v) (by norm_num : (0 : ℝ) ≤ 1)
  have hterm : |2*H*u*v| ≤ 2*H := by
    calc
      _ = 2*H*(|u| * |v|) := by
        rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*H)]
        ring
      _ ≤ 2*H*1 := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 2*H := mul_one _
  exact le_trans (abs_add_le _ _) (add_le_add he hterm)

theorem metric_component_bound (a x : Cartesian.Space) (hr : 1 ≤ Cartesian.radius a x)
    (i j : Fin 4) : |metric 1 a x i j| ≤ 3 := by
  obtain ⟨hH,hHu⟩ := unit_mass_potential_bounds a x hr
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have he : |Cartesian.eta i j| ≤ 1 := by
    unfold Cartesian.eta
    split_ifs <;> norm_num
  have hb := rank_entry_bound (Cartesian.eta i j) (Cartesian.potential 1 a x)
    (Cartesian.ell a x i) (Cartesian.ell a x j) he hH
    (ell_component_abs_le_one a x hr0 i) (ell_component_abs_le_one a x hr0 j)
  change |Cartesian.eta i j+2*Cartesian.potential 1 a x*Cartesian.ell a x i*Cartesian.ell a x j| ≤ 3
  linarith

theorem inverse_component_bound (a x : Cartesian.Space) (hr : 1 ≤ Cartesian.radius a x)
    (i j : Fin 4) : |(metric 1 a x)⁻¹ i j| ≤ 3 := by
  obtain ⟨hH,hHu⟩ := unit_mass_potential_bounds a x hr
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have he : |minkowski i j| ≤ 1 := by
    simp only [minkowski,Matrix.diagonal_apply,signature]
    split_ifs <;> norm_num
  have hb := rank_entry_bound (minkowski i j) (Cartesian.potential 1 a x)
    (-raisedEll a x i) (raisedEll a x j) he hH
    (by simpa only [abs_neg] using raisedEll_component_abs_le_one a x hr0 i)
    (raisedEll_component_abs_le_one a x hr0 j)
  rw [inverse_eq_explicit 1 a x hr0]
  simp only [explicitInverse,Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  calc
    _ = |minkowski i j+2*Cartesian.potential 1 a x*(-raisedEll a x i)*raisedEll a x j| := by
      congr 1
      ring
    _ ≤ 1+2*Cartesian.potential 1 a x := hb
    _ ≤ 3 := by linarith

theorem spatial_metric_condition_bound (a x v : Cartesian.Space)
    (hr : 1 ≤ Cartesian.radius a x) :
    dotProduct v v ≤ ADM.spatial (metric 1 a x) v v ∧
      ADM.spatial (metric 1 a x) v v ≤ 3*dotProduct v v := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  obtain ⟨hH,hHu⟩ := unit_mass_potential_bounds a x hr
  let l := Cartesian.spatialEll a x
  have hl : dotProduct l l = 1 := by
    have hu := spatialEll_unit a x hr0
    linarith
  have hp : 0 ≤ dotProduct (v-(dotProduct l v) • l) (v-(dotProduct l v) • l) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((v-(dotProduct l v) • l) i))
  simp only [sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,hl,
    dotProduct_comm v l] at hp
  have hcs : (dotProduct l v)^2 ≤ dotProduct v v := by nlinarith
  have hterm : 2*Cartesian.potential 1 a x*(dotProduct l v)^2 ≤ 2*dotProduct v v := by
    calc
      _ ≤ 2*1*(dotProduct l v)^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHu (by norm_num)) (sq_nonneg _)
      _ ≤ 2*dotProduct v v := by nlinarith
  rw [spatial_metric_form]
  change dotProduct v v ≤ dotProduct v v+2*Cartesian.potential 1 a x*(dotProduct l v)^2 ∧
    dotProduct v v+2*Cartesian.potential 1 a x*(dotProduct l v)^2 ≤ 3*dotProduct v v
  constructor
  · nlinarith [mul_nonneg hH (sq_nonneg (dotProduct l v))]
  · linarith

theorem hamiltonian_tangent_component_bound (a x : Cartesian.Space) (p : Fin 4 → ℝ)
    (P : ℝ) (hr : 1 ≤ Cartesian.radius a x)
    (hp : ∀ j, |p j| ≤ P) (i : Fin 4) :
    |(((metric 1 a x)⁻¹).mulVec p) i| ≤ 12*P := by
  simp only [Matrix.mulVec,dotProduct]
  calc
    _ ≤ ∑ j : Fin 4, |(metric 1 a x)⁻¹ i j*p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, 3*P := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (inverse_component_bound a x hr i j) (hp j) (abs_nonneg _) (by norm_num)
    _ = 12*P := by simp; ring

end BlackHole.KerrField
