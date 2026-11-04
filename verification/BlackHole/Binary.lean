module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import BlackHole.Curvature
import Mathlib.Tactic.NormNum

@[expose] public section

namespace BlackHole.Binary

abbrev Index := Fin 4
abbrev Tensor := Index → Index → ℚ

def delta (i j : Index) : ℚ := if i = j then 1 else 0
def eta (i j : Index) : ℚ := if i = j then (if i = 0 then -1 else 1) else 0
def offset (s : ℚ) (i : Index) : ℚ := if i = 1 then s else 0

/- Exact values and analytic first/second derivatives of one stationary,
   nonspinning Kerr-Schild source at local Cartesian position (s,0,0).
   g00 correction = 2m/r, g0i = 2m xi/r², gij correction = 2m xi xj/r³.
   Derivative index 0 is time and vanishes for this frozen metric. -/
def source (m s : ℚ) (i j : Index) : ℚ :=
  let r := |s|
  if i = 0 ∧ j = 0 then 2*m/r
  else if i = 0 then 2*m*offset s j/r^2
  else if j = 0 then 2*m*offset s i/r^2
  else 2*m*offset s i*offset s j/r^3

def sourceD (m s : ℚ) (e i j : Index) : ℚ :=
  let r := |s|
  let x := offset s
  if e = 0 then 0
  else if i = 0 ∧ j = 0 then -2*m*x e/r^3
  else if i = 0 then 2*m*(delta j e/r^2 - 2*x j*x e/r^4)
  else if j = 0 then 2*m*(delta i e/r^2 - 2*x i*x e/r^4)
  else 2*m*((delta i e*x j + delta j e*x i)/r^3 - 3*x i*x j*x e/r^5)

def sourceDD (m s : ℚ) (e f i j : Index) : ℚ :=
  let r := |s|
  let x := offset s
  if e = 0 ∨ f = 0 then 0
  else if i = 0 ∧ j = 0 then 2*m*(3*x e*x f/r^5 - delta e f/r^3)
  else if i = 0 then 2*m*(-2*(delta j e*x f + delta j f*x e + delta e f*x j)/r^4 +
    8*x j*x e*x f/r^6)
  else if j = 0 then 2*m*(-2*(delta i e*x f + delta i f*x e + delta e f*x i)/r^4 +
    8*x i*x e*x f/r^6)
  else 2*m*((delta i e*delta j f + delta i f*delta j e)/r^3 -
    3*((delta i e*x j + delta j e*x i)*x f +
       (delta i f*x j + delta j f*x i)*x e + delta e f*x i*x j)/r^5 +
    15*x i*x j*x e*x f/r^7)

def metric (binary : Bool) (i j : Index) : ℚ :=
  eta i j + if binary then source (1/2) 7 i j + source (1/2) (-7) i j
    else source 1 7 i j

def metricD (binary : Bool) (e i j : Index) : ℚ :=
  if binary then sourceD (1/2) 7 e i j + sourceD (1/2) (-7) e i j
    else sourceD 1 7 e i j

def metricDD (binary : Bool) (e f i j : Index) : ℚ :=
  if binary then sourceDD (1/2) 7 e f i j + sourceDD (1/2) (-7) e f i j
    else sourceDD 1 7 e f i j

def inverse (binary : Bool) (i j : Index) : ℚ :=
  if binary then
    if i = j then (if i = 0 then -7/5 else if i = 1 then 7/9 else 1) else 0
  else
    let raised (a : Index) : ℚ := if a = 0 then -1 else if a = 1 then 1 else 0
    eta i j - (2/7)*raised i*raised j

def inverseD (binary : Bool) (e a b : Index) : ℚ :=
  Curvature.inverseD (inverse binary) (metricD binary) e a b

def christoffel (binary : Bool) (a b c : Index) : ℚ :=
  Curvature.christoffel (inverse binary) (metricD binary) a b c

def christoffelD (binary : Bool) (e a b c : Index) : ℚ :=
  Curvature.christoffelD (inverse binary) (metricD binary) (metricDD binary) e a b c

def ricci (binary : Bool) (b c : Index) : ℚ :=
  Curvature.ricci (inverse binary) (metricD binary) (metricDD binary) b c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem inverse_checked :
    (∀ i j : Index, (∑ k : Index, metric true i k * inverse true k j) = delta i j) ∧
    (∀ i j : Index, (∑ k : Index, metric false i k * inverse false k j) = delta i j) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem single_ricci_tt : ricci false 0 0 = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem binary_ricci_tt : ricci true 0 0 = 4/3087 := by decide +kernel

theorem binary_not_vacuum : ricci true 0 0 ≠ 0 := by
  rw [binary_ricci_tt]
  norm_num

end BlackHole.Binary
