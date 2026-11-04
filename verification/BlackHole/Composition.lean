module

public import BlackHole.Transfer

@[expose] public section
noncomputable section

namespace BlackHole

def rotate (axis : Fin 3 → ℝ) (angle : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Real.cos angle • p+Real.sin angle • crossProduct axis p+
    ((1-Real.cos angle)*dotProduct axis p) • axis

theorem faraday_generator_preserves_norm (q u v rx ry rz : ℝ) :
    q * (ry * v - rz * u) + u * (rz * q - rx * v) +
      v * (rx * u - ry * q) = 0 := by ring

theorem rodrigues_preserves_norm (c s d pp : ℝ) (hcs : c*c + s*s = 1) :
    c*c*pp + s*s*(pp-d*d) + (1-c)^2*d*d + 2*c*(1-c)*d*d = pp := by
  linear_combination (pp - d*d) * hcs

theorem faraday_rotation_preserves_norm (axis p : Fin 3 → ℝ) (theta : ℝ)
    (haxis : dotProduct axis axis = 1) :
    let rotated := Real.cos theta • p + Real.sin theta • crossProduct axis p +
      ((1 - Real.cos theta) * dotProduct axis p) • axis
    dotProduct rotated rotated = dotProduct p p := by
  dsimp
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, dot_self_cross, dot_cross_self, cross_dot_cross,
    dotProduct_comm p axis, dotProduct_comm (crossProduct axis p) p,
    dotProduct_comm (crossProduct axis p) axis, haxis]
  have hcs : Real.cos theta * Real.cos theta + Real.sin theta * Real.sin theta = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  convert rodrigues_preserves_norm (Real.cos theta) (Real.sin theta)
    (dotProduct axis p) (dotProduct p p) hcs using 1
  ring

theorem rotate_zero (axis p : Fin 3 → ℝ) : rotate axis 0 p = p := by
  simp [rotate]

theorem rotate_derivative (axis p : Fin 3 → ℝ) (w t : ℝ)
    (haxis : dotProduct axis axis = 1) (i : Fin 3) :
    HasDerivAt (fun s => rotate axis (w*s) p i)
      (w*crossProduct axis (rotate axis (w*t) p) i) t := by
  have hc := ((hasDerivAt_id' t).const_mul w).cos
  have hs := ((hasDerivAt_id' t).const_mul w).sin
  have h := ((hc.mul_const (p i)).add (hs.mul_const (crossProduct axis p i))).add
    (((hc.const_sub 1).mul_const (dotProduct axis p)).mul_const (axis i))
  simp only [mul_one, Pi.add_def] at h
  convert h using 1
  · rfl
  · simp only [rotate, map_add, map_smul, cross_cross_eq_smul_sub_smul', cross_self,
      haxis, smul_zero, Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

def homogeneous (axis p : Fin 3 → ℝ) (alpha w s : ℝ) : Fin 3 → ℝ :=
  Real.exp (-alpha*s) • rotate axis (w*s) p

theorem homogeneous_derivative (axis p : Fin 3 → ℝ) (alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (i : Fin 3) :
    HasDerivAt (fun t => homogeneous axis p alpha w t i)
      (w*crossProduct axis (homogeneous axis p alpha w s) i-
        alpha*homogeneous axis p alpha w s i) s := by
  have he := ((hasDerivAt_id' s).const_mul (-alpha)).exp
  have h := he.mul (rotate_derivative axis p w s haxis i)
  simp only [mul_one, Pi.mul_def] at h
  convert h using 1
  · rfl
  · simp only [homogeneous, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

def transferCell (axis j : Fin 3 → ℝ) (alpha w s : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  homogeneous axis p alpha w s+cellPolarization axis j alpha w s

theorem transferCell_zero (axis j p : Fin 3 → ℝ) (alpha w : ℝ) :
    transferCell axis j alpha w 0 p = p := by
  simp [transferCell, homogeneous, rotate_zero, cellPolarization_zero]

theorem transferCell_derivative (axis j p : Fin 3 → ℝ) (alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (hd : alpha^2+w^2 ≠ 0) (i : Fin 3) :
    HasDerivAt (fun t => transferCell axis j alpha w t p i)
      (w*crossProduct axis (transferCell axis j alpha w s p) i-
        alpha*transferCell axis j alpha w s p i+j i) s := by
  have h := (homogeneous_derivative axis p alpha w s haxis i).add
    (cellPolarization_solves_transfer axis j alpha w s haxis hd i)
  simp only [Pi.add_def] at h
  convert h using 1
  · rfl
  · simp only [transferCell, map_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Splitting a homogeneous cell at any position gives the same exact
    transfer solution; this is independent of a numerical subdivision. -/
theorem transferCell_composes (axis j p : Fin 3 → ℝ) (alpha w x y : ℝ)
    (haxis : dotProduct axis axis = 1) (hd : alpha^2+w^2 ≠ 0) :
    transferCell axis j alpha w (x+y) p =
      transferCell axis j alpha w y (transferCell axis j alpha w x p) := by
  let left := fun t => transferCell axis j alpha w (x+t) p
  let right := fun t => transferCell axis j alpha w t (transferCell axis j alpha w x p)
  have hleft (t : ℝ) (i : Fin 3) : HasDerivAt (fun s => left s i)
      (crossProduct (w • axis) (left t) i-alpha*left t i+j i) t := by
    have h := (transferCell_derivative axis j p alpha w (x+t) haxis hd i).comp t
      ((hasDerivAt_id' t).const_add x)
    simpa only [left, Function.comp_def, LinearMap.map_smul, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul, mul_one] using h
  have hright (t : ℝ) (i : Fin 3) : HasDerivAt (fun s => right s i)
      (crossProduct (w • axis) (right t) i-alpha*right t i+j i) t := by
    have h := transferCell_derivative axis j (transferCell axis j alpha w x p) alpha w t haxis hd i
    simpa only [right, LinearMap.map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] using h
  exact polarized_transfer_unique left right (w • axis) j alpha hleft hright
    (by simp [left, right, transferCell_zero]) y

/-- Foreground operators multiply camera-outward, as in the render loop.
    Different cells need not commute. -/
theorem foreground_order {V : Type*} [AddCommGroup V] [Module ℝ V]
    (near far : V →ₗ[ℝ] V) (nearEmission farEmission background : V) :
    nearEmission+near (farEmission+far background) =
      nearEmission+near farEmission+(near.comp far) background := by
  simp [map_add, add_assoc]

end BlackHole
