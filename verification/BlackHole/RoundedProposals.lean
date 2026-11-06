module
public import BlackHole.CheckedFunction

/-! Computable interval proposals for the checked evaluator. They round
outward to multiples of 2^-prec, but nothing depends on that: every proposal
is re-checked exactly by `IntervalJet`, so these definitions need no proofs.

The compiler gives a definition the full arity of its function-typed result,
so a table built in such a definition is rebuilt at every lookup. Tables are
therefore built only inside definitions returning arrays or structures, and
exposed through `CheckedFunction.lookup` over the finished array. -/

@[expose] public section
namespace BlackHole.RoundedProposals
open DyadicInterval IntervalJet CheckedFunction

def zero : Bounds := ⟨0,0⟩

def down (prec : ℕ) (x : Dyadic) : Dyadic := x.roundDown prec
def up (prec : ℕ) (x : Dyadic) : Dyadic := x.roundUp prec

def addI (prec : ℕ) (a b : Bounds) : Bounds := ⟨down prec (a.lo+b.lo),up prec (a.hi+b.hi)⟩

def mulI (prec : ℕ) (a b : Bounds) : Bounds :=
  let p1 := a.lo*b.lo
  let p2 := a.lo*b.hi
  let p3 := a.hi*b.lo
  let p4 := a.hi*b.hi
  ⟨down prec (min (min p1 p2) (min p3 p4)),up prec (max (max p1 p2) (max p3 p4))⟩

/-- Reciprocal of a positive interval; anything else fails its later check. -/
def positiveRecip (prec : ℕ) (a : Bounds) : Bounds :=
  ⟨Dyadic.divAtPrec 1 a.hi prec,Dyadic.divAtPrec 1 a.lo prec+Dyadic.ofIntWithPrec 1 prec⟩

def recipI (prec : ℕ) (a : Bounds) : Bounds :=
  if 0 < a.lo then positiveRecip prec a
  else if a.hi < 0 then negate (positiveRecip prec (negate a))
  else zero

def sqrtDown (prec : ℕ) (x : Dyadic) : Dyadic :=
  if x ≤ 0 then 0 else Dyadic.ofIntWithPrec (Nat.sqrt (x.toRat*4^prec).floor.toNat) prec

def sqrtUp (prec : ℕ) (x : Dyadic) : Dyadic :=
  if x ≤ 0 then 0 else Dyadic.ofIntWithPrec (Nat.sqrt (x.toRat*4^prec).ceil.toNat+1) prec

def sqrtI (prec : ℕ) (a : Bounds) : Bounds := ⟨sqrtDown prec a.lo,sqrtUp prec a.hi⟩

/-- Running sums of the terms, starting from zero; one more entry than terms. -/
def accumulate (prec : ℕ) (terms : Array Bounds) : Array Bounds :=
  terms.foldl (fun acc t => acc.push (addI prec (acc.getD (acc.size-1) zero) t)) #[zero]

def convolution (prec : ℕ) (a b : ℕ → Bounds) (k : ℕ) : ConvolutionRow :=
  let terms := Array.ofFn (n := k+1) (fun i => mulI prec (a i) (b (k-i)))
  ⟨lookup terms,lookup (accumulate prec terms)⟩

def emptyQuotient : QuotientRow := ⟨⟨fun _ => zero,fun _ => zero⟩,zero,zero⟩

def division (prec N : ℕ) (a b : ℕ → Bounds) : DivisionProposal :=
  let inverse := recipI prec (b 0)
  let step := fun (acc : Array Bounds × Array QuotientRow) (k : ℕ) =>
    let c := acc.1
    let terms := Array.ofFn (n := k) (fun i => mulI prec (b (i+1)) (c.getD (k-(i+1)) zero))
    let sums := accumulate prec terms
    let difference := addI prec (a k) (negate (lookup sums k))
    let row : QuotientRow := ⟨⟨lookup terms,lookup sums⟩,difference,inverse⟩
    (c.push (mulI prec difference inverse),acc.2.push row)
  let built := (List.range (N+1)).foldl step (#[],#[])
  ⟨lookup built.1,fun k => built.2.getD k emptyQuotient⟩

def root (prec N : ℕ) (a : ℕ → Bounds) : RootProposal :=
  let c0 := sqrtI prec (a 0)
  let denominator := mulI prec two c0
  let inverse := recipI prec denominator
  let step := fun (acc : Array Bounds × Array RootRow) (k : ℕ) =>
    let c := acc.1
    let terms := Array.ofFn (n := k) (fun i => mulI prec (c.getD (i+1) zero) (c.getD (k-i) zero))
    let sums := accumulate prec terms
    let difference := addI prec (a (k+1)) (negate (lookup sums k))
    let row : RootRow := ⟨⟨⟨lookup terms,lookup sums⟩,difference,inverse⟩,denominator⟩
    (c.push (mulI prec difference inverse),acc.2.push row)
  let built := (List.range N).foldl step (#[c0],#[])
  ⟨lookup built.1,fun k => built.2.getD k ⟨emptyQuotient,zero⟩⟩

def proposals (prec N : ℕ) : Proposals where
  addition := fun a b => Array.ofFn (n := N+1) (fun k => addI prec (a k) (b k))
  multiplication := fun a b => Array.ofFn (n := N+1) (fun k => convolution prec a b k)
  division := division prec N
  root := root prec N

end BlackHole.RoundedProposals
