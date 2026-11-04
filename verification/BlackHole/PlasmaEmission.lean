module

public import BlackHole.Plasma
public import BlackHole.Models
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace BlackHole.Plasma

def clamp01 (x : ℝ) : ℝ := min (max x 0) 1

theorem clamp01_bounds (x : ℝ) : 0 ≤ clamp01 x ∧ clamp01 x ≤ 1 :=
  ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

def colorMix (a b w : ℝ) : ℝ := (1-w)*a+w*b

theorem colorMix_nonnegative (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ colorMix a b w := by
  exact add_nonneg (mul_nonneg (by linarith) ha) (mul_nonneg hw hb)

def blackbodyColor (temperature : ℝ) (i : Fin 3) : ℝ :=
  let s := clamp01 temperature
  if s < 2/5 then
    colorMix (![1/20, 0, 0] i) (![1, 7/20, 1/50] i) (s/(2/5))
  else if s < 3/4 then
    colorMix (![1, 7/20, 1/50] i) (![1, 19/20, 4/5] i) ((s-2/5)/(7/20))
  else
    colorMix (![1, 19/20, 4/5] i) (![13/20, 4/5, 1] i) ((s-3/4)/(1/4))

theorem blackbodyColor_nonnegative (temperature : ℝ) (i : Fin 3) :
    0 ≤ blackbodyColor temperature i := by
  obtain ⟨hlo,hhi⟩ := clamp01_bounds temperature
  dsimp only [blackbodyColor]
  split_ifs with hlow hmid
  · apply colorMix_nonnegative
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
    · positivity
    · linarith
  · apply colorMix_nonnegative
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
    · linarith
    · linarith
  · apply colorMix_nonnegative
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
    · linarith
    · linarith

def hotWeight (model : ℕ) (argument : ℝ) : ℝ :=
  if model = 1 then (1-Real.tanh argument)/2 else 0

theorem hotWeight_bounds (model : ℕ) (argument : ℝ) :
    0 ≤ hotWeight model argument ∧ hotWeight model argument ≤ 1 := by
  unfold hotWeight
  split_ifs
  · constructor <;> linarith [Real.neg_one_lt_tanh argument, Real.tanh_lt_one argument]
  · norm_num

def plasmaDensity (z edge height : ℝ) : ℝ :=
  (2/5)*Real.exp (-(1/2)*z^2)*clamp01 edge/max height (1/10000)

theorem plasmaDensity_nonnegative (z edge height : ℝ) : 0 ≤ plasmaDensity z edge height := by
  have he := (clamp01_bounds edge).1
  have hh : 0 < max height (1/10000 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  unfold plasmaDensity
  positivity

def frequencyRatio (frequency energy : ℝ) : ℝ :=
  230/max (frequency/clampedRedshift energy) 1

theorem frequencyRatio_positive (frequency energy : ℝ) : 0 < frequencyRatio frequency energy := by
  have hd : 0 < max (frequency/clampedRedshift energy) 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  exact div_pos (by norm_num) hd

def thermalColor (model : ℕ) (argument temperature : ℝ) (i : Fin 3) : ℝ :=
  (1-hotWeight model argument)*blackbodyColor temperature i

def synchrotronColor (model : ℕ) (argument ratio perpendicular frequency energy : ℝ)
    (i : Fin 3) : ℝ :=
  hotWeight model argument*(clamp01 ratio)^(3/5 : ℝ)*clamp01 perpendicular*
    frequencyRatio frequency energy*(![1, 13/20, 3/10] i)

theorem thermalColor_nonnegative (model : ℕ) (argument temperature : ℝ) (i : Fin 3) :
    0 ≤ thermalColor model argument temperature i := by
  exact mul_nonneg (sub_nonneg.mpr (hotWeight_bounds model argument).2)
    (blackbodyColor_nonnegative temperature i)

theorem synchrotronColor_nonnegative (model : ℕ) (argument ratio perpendicular frequency energy : ℝ)
    (i : Fin 3) : 0 ≤ synchrotronColor model argument ratio perpendicular frequency energy i := by
  have hh := (hotWeight_bounds model argument).1
  have hr := Real.rpow_nonneg (clamp01_bounds ratio).1 (3/5 : ℝ)
  have hp := (clamp01_bounds perpendicular).1
  have hf := (frequencyRatio_positive frequency energy).le
  have hc : 0 ≤ (![1, 13/20, 3/10] : Fin 3 → ℝ) i := by fin_cases i <;> norm_num
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hh hr) hp) hf) hc

def luminance (rgb : Fin 3 → ℝ) : ℝ :=
  (2126/10000)*rgb 0+(7152/10000)*rgb 1+(722/10000)*rgb 2

theorem luminance_nonnegative (rgb : Fin 3 → ℝ) (hrgb : ∀ i, 0 ≤ rgb i) :
    0 ≤ luminance rgb :=
  emissivity_luminance_nonneg _ _ _ (hrgb 0) (hrgb 1) (hrgb 2)

theorem luminance_scaled_sum (a : ℝ) (rgb other : Fin 3 → ℝ) :
    luminance (fun i => a*(rgb i+other i)) = a*luminance rgb+a*luminance other := by
  unfold luminance
  ring

/-- Every exact-real emission branch has nonnegative opacity and a physical
    source Stokes vector, for arbitrary model and projected-field values. -/
theorem prescription_stokes_cone (model : ℕ)
    (argument temperature ratio perpendicular frequency energy z edge height bx by_ : ℝ) :
    let density := plasmaDensity z edge height
    let boost := (clampedRedshift energy)^3
    let thermal := thermalColor model argument temperature
    let synch := synchrotronColor model argument ratio perpendicular frequency energy
    let intensity := luminance (fun i => density*boost*(thermal i+synch i))
    let synchI := density*boost*luminance synch
    let den := max (bx^2+by_^2) (1/1000000000000)
    0 ≤ (7/10)*density ∧ 0 ≤ intensity ∧
      ((3/4)*synchI*(by_^2-bx^2)/den)^2+
        ((3/4)*synchI*(-2*bx*by_)/den)^2 ≤ intensity^2 := by
  dsimp only
  have hd := plasmaDensity_nonnegative z edge height
  have hb : 0 ≤ (clampedRedshift energy)^3 :=
    pow_nonneg (le_trans (by norm_num) (clamped_redshift_bounds energy).1) 3
  have ht := luminance_nonnegative _ (thermalColor_nonnegative model argument temperature)
  have hs := luminance_nonnegative _
    (synchrotronColor_nonnegative model argument ratio perpendicular frequency energy)
  rw [luminance_scaled_sum]
  exact ⟨mul_nonneg (by norm_num) hd,
    emission_stokes_cone bx by_ _ _ _ (mul_nonneg (mul_nonneg hd hb) ht)
      (mul_nonneg (mul_nonneg hd hb) hs) (by norm_num)⟩

end BlackHole.Plasma
