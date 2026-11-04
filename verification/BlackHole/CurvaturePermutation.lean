module

public import BlackHole.Curvature

@[expose] public section

namespace BlackHole.Curvature

variable {n R : Type*} [Fintype n] [Field R]

theorem inverseD_reindex (p : n ≃ n) (inv : Matrix n n R) (dg : n → Matrix n n R)
    (e a b : n) :
    inverseD (fun i j => inv (p i) (p j)) (fun d i j => dg (p d) (p i) (p j)) e a b =
      inverseD inv dg (p e) (p a) (p b) := by
  unfold inverseD
  congr 1
  calc
    _ = ∑ i, ∑ j, inv (p a) (p i)*dg (p e) (p i) j*inv j (p b) := by
      apply Finset.sum_congr rfl
      intro i _
      exact p.sum_comp (fun j => inv (p a) (p i)*dg (p e) (p i) j*inv j (p b))
    _ = _ := p.sum_comp (fun i => ∑ j, inv (p a) i*dg (p e) i j*inv j (p b))

theorem christoffel_reindex (p : n ≃ n) (inv : Matrix n n R) (dg : n → Matrix n n R)
    (a b c : n) :
    christoffel (fun i j => inv (p i) (p j)) (fun d i j => dg (p d) (p i) (p j)) a b c =
      christoffel inv dg (p a) (p b) (p c) := by
  unfold christoffel
  congr 1
  exact p.sum_comp (fun d => inv (p a) d*(dg (p b) d (p c)+dg (p c) d (p b)-dg d (p b) (p c)))

theorem christoffelD_reindex (p : n ≃ n) (inv : Matrix n n R)
    (dg : n → Matrix n n R) (ddg : n → n → Matrix n n R) (e a b c : n) :
    christoffelD (fun i j => inv (p i) (p j)) (fun d i j => dg (p d) (p i) (p j))
      (fun d f i j => ddg (p d) (p f) (p i) (p j)) e a b c =
      christoffelD inv dg ddg (p e) (p a) (p b) (p c) := by
  simp only [christoffelD, inverseD_reindex]
  congr 1
  exact p.sum_comp (fun d => inverseD inv dg (p e) (p a) d*
    (dg (p b) d (p c)+dg (p c) d (p b)-dg d (p b) (p c))+
    inv (p a) d*(ddg (p e) (p b) d (p c)+ddg (p e) (p c) d (p b)-ddg (p e) d (p b) (p c)))

theorem ricci_reindex (p : n ≃ n) (inv : Matrix n n R)
    (dg : n → Matrix n n R) (ddg : n → n → Matrix n n R) (b c : n) :
    ricci (fun i j => inv (p i) (p j)) (fun d i j => dg (p d) (p i) (p j))
      (fun d f i j => ddg (p d) (p f) (p i) (p j)) b c =
      ricci inv dg ddg (p b) (p c) := by
  simp only [ricci, christoffelD_reindex, christoffel_reindex]
  calc
    _ = ∑ a, (christoffelD inv dg ddg (p a) (p a) (p b) (p c)-
        christoffelD inv dg ddg (p c) (p a) (p b) (p a)+
        ∑ d, (christoffel inv dg (p a) (p a) d*christoffel inv dg d (p b) (p c)-
          christoffel inv dg (p a) (p c) d*christoffel inv dg d (p b) (p a))) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact p.sum_comp (fun d => christoffel inv dg (p a) (p a) d*christoffel inv dg d (p b) (p c)-
        christoffel inv dg (p a) (p c) d*christoffel inv dg d (p b) (p a))
    _ = _ := p.sum_comp (fun a => christoffelD inv dg ddg a a (p b) (p c)-
      christoffelD inv dg ddg (p c) a (p b) a+
      ∑ d, (christoffel inv dg a a d*christoffel inv dg d (p b) (p c)-
        christoffel inv dg a (p c) d*christoffel inv dg d (p b) a))

end BlackHole.Curvature
