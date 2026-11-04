module
public import BlackHole.KerrJetBridge

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

/- The residual is multiplied by |l|^2-1. Each component certificate is checked
   by ring against the source jets, with no symbolic solver in the trust base. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def spatialResidual (S r c m : ℝ) (l v : Cartesian.Space) (i j : Fin 3) : ℝ :=
  let N : ℝ := l 0^2+l 1^2+l 2^2
  let U : ℝ := dotProduct (twist l v) (twist l v)
  let D : ℝ := -m*r*(16*N^4*U*c^2*m^3*r^3 - 16*N^3*S*U*c^2*m^2*r^2 - 48*N^3*U*c^2*m^3*r^3 -
    8*N^3*c^2*m^3*r^3 + 24*N^3*m^3*r^5 - 22*N^2*S^2*U*c^2*m*r + 6*N^2*S^2*U*m*r^3 +
    32*N^2*S*U*c^2*m^2*r^2 + 8*N^2*S*c^2*m^2*r^2 - 24*N^2*S*m^2*r^4 + 48*N^2*U*c^2*m^3*r^3 +
    16*N^2*c^2*m^3*r^3 - 48*N^2*m^3*r^5 + 9*N*S^3*U*c^2 - 3*N*S^3*U*r^2 + 4*N*S^3*m*r +
    22*N*S^2*U*c^2*m*r - 6*N*S^2*U*m*r^3 - 16*N*S^2*m*r^3 - 16*N*S*U*c^2*m^2*r^2 - 8*N*S*c^2*m^2*r^2
    + 24*N*S*m^2*r^4 - 16*N*U*c^2*m^3*r^3 - 8*N*c^2*m^3*r^3 + 24*N*m^3*r^5 - 2*S^4 + 5*S^3*c^2 +
    5*S^3*r^2 + 6*S^2*c^2*m*r + 6*S^2*m*r^3)
  let LL : ℝ := m^2*(16*N^3*U*c^2*m^2*r^4 - 24*N^2*S*U*c^2*m*r^3 - 48*N^2*U*c^2*m^2*r^4 -
    8*N^2*c^2*m^2*r^4 + 24*N^2*m^2*r^6 - 18*N*S^2*U*c^2*r^2 + 6*N*S^2*U*r^4 - 2*N*S*U*c^4*m*r +
    44*N*S*U*c^2*m*r^3 - 2*N*S*U*m*r^5 + 2*N*S*c^4*m*r - 18*N*S*m*r^5 + 48*N*U*c^2*m^2*r^4 -
    4*N*c^4*m^2*r^2 + 32*N*c^2*m^2*r^4 - 60*N*m^2*r^6 + 4*S^3*r^2 + S^2*U*c^4 + 20*S^2*U*c^2*r^2 -
    5*S^2*U*r^4 - S^2*c^4 + 8*S^2*c^2*r^2 - 7*S^2*r^4 + 2*S*U*c^4*m*r - 20*S*U*c^2*m*r^3 +
    2*S*U*m*r^5 + 4*S*c^4*m*r - 16*S*c^2*m*r^3 + 28*S*m*r^5 - 16*U*c^2*m^2*r^4 + 4*c^4*m^2*r^2 -
    24*c^2*m^2*r^4 + 36*m^2*r^6)
  let TT : ℝ := -m*(-16*N^4*c^2*m^3*r^4 + 16*N^3*S*c^2*m^2*r^3 + 4*N^3*c^4*m^3*r^2 +
    40*N^3*c^2*m^3*r^4 + 4*N^3*m^3*r^6 + 22*N^2*S^2*c^2*m*r^2 - 6*N^2*S^2*m*r^4 - 4*N^2*S*c^4*m^2*r
    - 24*N^2*S*c^2*m^2*r^3 - 4*N^2*S*m^2*r^5 - 12*N^2*c^4*m^3*r^2 - 24*N^2*c^2*m^3*r^4 -
    12*N^2*m^3*r^6 - 9*N*S^3*c^2*r + 3*N*S^3*r^3 - N*S^2*c^4*m - 2*N*S^2*c^2*m*r^2 - N*S^2*m*r^4 +
    8*N*S*c^4*m^2*r + 8*N*S*m^2*r^5 + 12*N*c^4*m^3*r^2 - 8*N*c^2*m^3*r^4 + 12*N*m^3*r^6 -
    9*S^3*c^2*r + 3*S^3*r^3 + S^2*c^4*m - 20*S^2*c^2*m*r^2 + 7*S^2*m*r^4 - 4*S*c^4*m^2*r +
    8*S*c^2*m^2*r^3 - 4*S*m^2*r^5 - 4*c^4*m^3*r^2 + 8*c^2*m^3*r^4 - 4*m^3*r^6)
  let LT : ℝ := m*(4*N^2*c^4*m^3*r^2 - 16*N^2*c^2*m^3*r^4 + 12*N^2*m^3*r^6 - 2*N*S^3*m*r^2 +
    4*N*S^2*m*r^4 - 4*N*S*c^4*m^2*r + 12*N*S*c^2*m^2*r^3 - 8*N*S*m^2*r^5 - 8*N*c^4*m^3*r^2 +
    32*N*c^2*m^3*r^4 - 24*N*m^3*r^6 - S^4*r + 10*S^3*c^2*r + 2*S^3*m*r^2 - 2*S^3*r^3 - S^2*c^4*m +
    20*S^2*c^2*m*r^2 - 11*S^2*m*r^4 + 4*S*c^4*m^2*r - 12*S*c^2*m^2*r^3 + 8*S*m^2*r^5 + 4*c^4*m^3*r^2
    - 16*c^2*m^3*r^4 + 12*m^3*r^6)
  let LC : ℝ := 2*c*m*r*(-4*N^2*c^2*m^3*r^2 + 12*N^2*m^3*r^4 + 2*N*S^2*m*r^2 + 4*N*S*c^2*m^2*r -
    8*N*S*m^2*r^3 + 8*N*c^2*m^3*r^2 - 24*N*m^3*r^4 - S^3*r + 4*S^2*c^2*m - 12*S^2*m*r^2 -
    4*S*c^2*m^2*r + 8*S*m^2*r^3 - 4*c^2*m^3*r^2 + 12*m^3*r^4)
  let TC : ℝ := -c*m*(-8*N^3*c^2*m^3*r^3 + 8*N^3*m^3*r^5 + 8*N^2*S*c^2*m^2*r^2 - 8*N^2*S*m^2*r^4 +
    24*N^2*c^2*m^3*r^3 - 24*N^2*m^3*r^5 + 8*N*S^2*c^2*m*r - 20*N*S^2*m*r^3 - 16*N*S*c^2*m^2*r^2 +
    16*N*S*m^2*r^4 - 24*N*c^2*m^3*r^3 + 24*N*m^3*r^5 - 3*S^3*c^2 + 9*S^3*r^2 - 8*S^2*c^2*m*r +
    20*S^2*m*r^3 + 8*S*c^2*m^2*r^2 - 8*S*m^2*r^4 + 8*c^2*m^3*r^3 - 8*m^3*r^5)
  let EL : ℝ := 2*S^2*c*m*r^2*(2*N*m*r - S - 2*m*r)
  let ET : ℝ := 2*N*S^2*c*m*r^2*(2*N*m*r - S - 2*m*r)
  let EC : ℝ := -S^2*m*r*(-S + 2*r^2)*(2*N*m*r - S - 2*m*r)
  D*Cartesian.basis i j+LL*l i*l j+TT*twist l v i*twist l v j+
    LT*(l i*twist l v j+twist l v i*l j)+
    LC*(l i*cosineD l v j+cosineD l v i*l j)+
    TC*(twist l v i*cosineD l v j+cosineD l v i*twist l v j)+
    EL*crossProduct l (Cartesian.basis j) i+
    ET*crossProduct (twist l v) (Cartesian.basis j) i+
    EC*crossProduct (cosineD l v) (Cartesian.basis j) i

end BlackHole.KerrVacuumJet
