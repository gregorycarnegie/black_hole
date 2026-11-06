import BlackHole.RayCertificate

/-! Command-line certified ray tracer. Everything here except the final
`RayCertificate.certify` call is an untrusted search: it proposes step
lengths, Taylor coefficients, weights, tube radii and rounded observables.
The printed verdict comes only from `certify`, whose meaning is the theorem
`RayCertificate.certified_ray`. -/

open BlackHole DyadicInterval KerrProgram StepField StepCheck TraceCheck RayEvents RayObserve
  RayCertificate

def prec : ℕ := 96

def pointB (v : Dyadic) : Bounds := ⟨v,v⟩
def half : Dyadic := Dyadic.ofIntWithPrec 1 1
def mid (b : Bounds) : Dyadic := ((b.lo+b.hi)*half).roundDown 64
def magB (b : Bounds) : Dyadic := dmax (mag b.lo) (mag b.hi)

/-! ### Decimal input and binary32 output -/

def parseNat? (s : String) : Option ℕ := if s.isEmpty then some 0 else s.toNat?

def parseRat? (s : String) : Option Rat := do
  let (neg,body) := if s.startsWith "-" then (true,(s.drop 1).toString) else (false,s)
  let (mant,ex) := match body.splitOn "e" with
    | [m] => (m,"0")
    | [m,e] => (m,e)
    | _ => ("","")
  let e ← if ex.startsWith "-" then (ex.drop 1).toString.toNat?.map (fun n => -(n:Int)) else ex.toNat?.map (fun n => (n:Int))
  let (ip,fp) := match mant.splitOn "." with
    | [i] => (i,"")
    | [i,f] => (i,f)
    | _ => ("x","")
  let i ← parseNat? ip
  let f ← parseNat? fp
  let scale : Rat := (10:Rat)^fp.length
  let v : Rat := (i:Rat)+(f:Rat)/scale
  let v := if e ≥ 0 then v*(10:Rat)^e.toNat else v/(10:Rat)^(-e).toNat
  pure (if neg then -v else v)

/-- Inputs are rounded once to 2^-64; the certificate is about these exact values. -/
def toDyadic (q : Rat) : Dyadic := Rat.toDyadic q 64

/-- Round a rational to the nearest binary32 value (normal range; ties to even). -/
def roundBinary32 (q : Rat) : Dyadic :=
  if q == 0 then 0 else
  let a := if q < 0 then -q else q
  let e0 : Int := (Nat.log2 a.num.natAbs : Int)-(Nat.log2 a.den : Int)
  let e := if a < (2:Rat)^e0 then e0-1 else if a ≥ (2:Rat)^(e0+1) then e0+1 else e0
  let shift := 23-e
  let scaled := if shift ≥ 0 then a*(2:Rat)^shift.toNat else a/(2:Rat)^(-shift).toNat
  let fl := scaled.floor
  let frac := scaled-fl
  let m := if frac > 1/2 || (frac == 1/2 && fl % 2 == 1) then fl+1 else fl
  let d := Dyadic.ofIntWithPrec m shift
  if q < 0 then -d else d

def showD (d : Dyadic) : String :=
  let q := d.toRat
  let sign := if q < 0 then "-" else ""
  let a := if q < 0 then -q else q
  let scaled := (a*(10:Rat)^12).floor
  let ip := scaled/(10^12:Int)
  let fp := toString (scaled % (10^12:Int))
  s!"{sign}{ip}.{"".pushn '0' (12-fp.length)}{fp}"

def showB (b : Bounds) : String := s!"{showD (mid b)} ± {showD ((b.hi-b.lo)*half)}"

/-! ### Untrusted step proposals -/

def taylor (spin : Fin 3 → Dyadic) (PT : Bounds) (y : Fin 10 → Dyadic) :
    Option (Fin 10 → Fin 5 → Dyadic) := do
  let mut A : Array (Fin 10 → Dyadic) := #[y]
  for n in [1:5] do
    let prev := A
    let input : KerrProgram.State CheckedData.Data :=
      assemble (boxD PT) (fun i => some (fun k => if h : k < prev.size then pointB ((prev[k]'h) i) else ⟨0,0⟩))
    let coeffs ← collect (components (run prec (n-1) spin input))
    A := A.push (fun i => Dyadic.divAtPrec (mid (coeffs i (n-1))) (n : Dyadic) 80)
  return fun i k => (A.getD k (fun _ => 0)) i

def weights (y : Fin 10 → Dyadic) : Fin 10 → Dyadic := fun i =>
  let group : List (Fin 10) := if i.val < 3 then [0,1,2] else if i.val < 6 then [3,4,5] else [6,7,8,9]
  group.foldl (fun m j => dmax m (mag (y j))) 1

def ten7 : Dyadic := 10000000
def ten11 : Dyadic := 100000000000

/-- Residual-only diagnostics, recomputed exactly as `check` does. -/
def defectOf (spin : Fin 3 → Dyadic) (PT : Bounds) (s : Step) : Option Dyadic := do
  let start := run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 0) (boxD PT))
  let along := run prec 4 spin (stepInput (ops prec 4) s.A (timeD 0 s.h) (boxD PT))
  let point ← collect (components start)
  let box ← collect (components along)
  pure (maxOf fun i => divUp prec (residualBound s i (point i) (box i)) (s.w i))

def lipschitzOf (spin : Fin 3 → Dyadic) (PT : Bounds) (s : Step) : Option Dyadic := do
  let path ← collect fun i => horner (ops prec 0) (s.A i) (timeD 0 s.h)
  let T := tubeBox s path
  let D ← collect fun j =>
    collect (components (run prec 1 spin (assemble (boxD PT) (fun k => lineD (T k) (unit j k)))))
  pure (maxOf fun i => divUp prec (rowBound s D i) (s.w i))

/-- The weighted end error radius that `check` used for the final box. -/
def endRadius (r : Result) (h : Dyadic) : Dyadic := divUp prec (r.e0+h*r.defect) (1-h*r.lipschitz)

inductive Failure where
  | arithmetic | budget | domain | event | stepLimit
  deriving Repr

def Failure.name : Failure → String
  | .arithmetic => "arithmetic" | .budget => "accuracy budget" | .domain => "outside domain"
  | .event => "event boundary" | .stepLimit => "step limit"

/-- Propose and check one step of length `h`; returns the step, its result and verdict. -/
def attempt (spin : Fin 3 → Dyadic) (PT : Bounds) (X : Fin 10 → Bounds) (h : Dyadic)
    (hint : Option (Dyadic × Dyadic)) : Except (Failure × String) (Step × Result × Verdict) := do
  -- Materialize every table: closures over earlier steps would be re-evaluated recursively.
  let Xv := Vector.ofFn X
  let X := Xv.get
  let yv := Vector.ofFn fun i => mid (X i)
  let y := yv.get
  let some A0 := taylor spin PT y | throw (.arithmetic,"taylor")
  let Av := Vector.ofFn fun i => Vector.ofFn fun k => A0 i k
  let A : Fin 10 → Fin 5 → Dyadic := fun i k => (Av.get i).get k
  let wv := Vector.ofFn (weights y)
  let w := wv.get
  let e0 := maxOf fun i => divUp prec (gapD (A i 0) (X i)) (w i)
  -- Fast path: one check with a tube radius predicted from the previous step.
  if let some (δp,Kp) := hint then
    if 16*h*Kp < 1 then
      let rho := (2*(e0+h*δp)*(1+4*h*Kp)).roundUp prec
      if rho*ten7 ≤ 40 && rho > 0 then
        if let some r := check prec spin PT X ⟨h,A,w,rho⟩ then
          if let some v := verdict prec spin r then
            if endRadius r h*ten7 ≤ 1 && r.defect*ten11 ≤ 1 then
              return (⟨h,A,w,rho⟩,r,v)
  let some δ := defectOf spin PT ⟨h,A,w,0⟩ | throw (.arithmetic,"defect")
  if δ*ten11 > 1 then throw (.budget,s!"defect {showD δ}")
  let mut rho := (2*(e0+h*δ)).roundUp prec
  if rho == 0 then rho := Dyadic.ofIntWithPrec 1 80
  for _ in [0:8] do
    if rho*ten7 > 40 then throw (.budget,s!"tube {showD rho}")
    let some K := lipschitzOf spin PT ⟨h,A,w,rho⟩ | throw (.domain,"tube")
    if 8*h*K ≥ 1 then throw (.budget,s!"lipschitz {showD K}")
    let need := e0+h*(δ+K*rho)
    if need ≤ rho then
      match check prec spin PT X ⟨h,A,w,rho⟩ with
      | none => throw (.arithmetic,"check")
      | some r =>
        if endRadius r h*ten7 > 1 then throw (.budget,s!"final {showD (endRadius r h)}")
        match verdict prec spin r with
        | none => throw (.event,"verdict")
        | some v => return (⟨h,A,w,rho⟩,r,v)
    rho := (2*need).roundUp prec
  throw (.budget,"tube iteration")

structure Trace where
  steps : Array Step := #[]
  last : Option (Result × Verdict) := none
  rejected : ℕ := 0
  failure : Option Failure := none

def maxStep : Dyadic := 32
def minStep : Dyadic := Dyadic.ofIntWithPrec 1 30

/-- Rust-style step control: double after success, halve after failure. -/
partial def trace (spin : Fin 3 → Dyadic) (PT : Bounds) (limit : Dyadic) (X : Fin 10 → Bounds)
    (elapsed h : Dyadic) (acc : Trace) (verbose : Bool) : IO Trace := do
  if acc.steps.size ≥ 10000 then return { acc with failure := some .stepLimit }
  let remaining := limit-elapsed
  if remaining ≤ 0 then return acc
  let h := if h > remaining then remaining else h
  let t0 ← IO.monoMsNow
  let hintv := acc.last.map fun (r,_) => (r.defect*16,r.lipschitz)
  let res := attempt spin PT X h hintv
  let t1 ← IO.monoMsNow
  match res with
  | .ok (s,r,v) =>
    if verbose then
      IO.eprintln s!"step {acc.steps.size+1}: t={showD elapsed} h={showD h} rho={showD s.rho} x0={showB (r.final 0)} {repr v} ({t1-t0} ms)"
    let finalv := Vector.ofFn r.final
    let r := { r with final := finalv.get }
    let acc := { acc with steps := acc.steps.push s, last := some (r,v) }
    if v != .running then return acc
    -- The defect grows faster than h^4 (its box widens): double only with a 32x margin.
    let grow := r.defect*32*ten11 ≤ 1
    let next := if grow then (if 2*h > maxStep then maxStep else 2*h) else h
    trace spin PT limit r.final (elapsed+h) next acc verbose
  | .error (f,why) =>
    if verbose then IO.eprintln s!"  reject h={showD h}: {f.name} {why} ({t1-t0} ms)"
    let acc := { acc with rejected := acc.rejected+1 }
    if h ≤ minStep then return { acc with failure := some f }
    trace spin PT limit X elapsed (h*half) acc verbose

def observation (spin : Fin 3 → Dyadic) (PT : Bounds) (B : Fin 10 → Bounds) : Option Observation := do
  let v : Fin 11 → CheckedData.Data := fun i => boxD (fullBox PT B i)
  let k ← (List.finRange 3).mapM fun i => spatialK spin (ops prec 0) v i
  let r ← redshiftP spin (ops prec 0) v
  let kv := k.toArray.map fun d => (mid (d 0)).toRat
  let n2 := kv.foldl (fun s x => s+x*x) 0
  -- Direction is reported unnormalized in binary32; the checker normalizes it exactly.
  let scale : Rat := if n2 == 0 then 1 else 1/(n2.floor.natAbs.sqrt+1)
  pure ⟨fun i => roundBinary32 (kv.getD i 0*scale),roundBinary32 (mid (r 0)).toRat⟩

def usage : String :=
  "usage: certify ray ax ay az  x y z  dx dy dz  hx hy hz  limit\n" ++
  "  spin vector, camera position, view direction, screen hint, affine limit (≤ 10000)"

def main (args : List String) : IO UInt32 := do
  match args with
  | "ray" :: rest =>
    let some vals := rest.mapM parseRat? | IO.println usage; return 2
    unless vals.length == 13 do IO.println usage; return 2
    let d := vals.toArray.map toDyadic
    let v3 (o : ℕ) : Fin 3 → Dyadic := fun i => d.getD (o+i) 0
    let spin := v3 0; let pos := v3 3; let dir := v3 6; let hint := v3 9
    let limit := d.getD 12 0
    let some (PT,X) := cameraBoxes prec spin pos dir hint
      | IO.println "unresolved: camera initialization failed"; return 1
    let t0 ← IO.monoMsNow
    let tr ← trace spin PT limit X 0 maxStep {} true
    let obs := match tr.last with
      | some (r,.escaped) => (observation spin PT r.final).getD ⟨fun _ => 0,0⟩
      | _ => ⟨fun _ => 0,0⟩
    let t1 ← IO.monoMsNow
    IO.println s!"steps accepted {tr.steps.size}, rejected {tr.rejected}, search {t1-t0} ms"
    if let some f := tr.failure then
      IO.println s!"unresolved: {f.name}"
      return 1
    match certify prec spin pos dir hint tr.steps.toList obs with
    | none =>
      IO.println "unresolved: certificate rejected"
      IO.println s!"  camera checks: {CameraPhysics.cameraChecks spin pos dir hint prec}"
      match checkTrace prec spin PT X tr.steps.toList with
      | none => IO.println "  trace check failed"
      | some (rs,v) =>
        IO.println s!"  trace check ok: {repr v}"
        if let some last := rs.getLast? then
          let vv : Fin 11 → CheckedData.Data := fun i => boxD (fullBox PT last.final i)
          let show? (d : CheckedData.Data) := match d with
            | some f => s!"[{showD (f 0).lo}, {showD (f 0).hi}]" | none => "fail"
          IO.println s!"  |k| {show? (kNormP spin (ops prec 0) vv)}"
          IO.println s!"  chord² {show? (chordSqP spin (ops prec 0) vv obs.direction)}"
          IO.println s!"  redshift {show? (redshiftP spin (ops prec 0) vv)} reported {showD obs.redshift}"
          IO.println s!"  screen norm-1 {show? (screenNormP spin (ops prec 0) vv)}"
          IO.println s!"  transversality {show? (transversalityP (ops prec 0) vv)}"
          IO.println s!"  observe {observe prec spin PT last.final obs}"
      return 1
    | some rep =>
      let t2 ← IO.monoMsNow
      IO.println s!"certified ({t2-t1} ms replay): {repr rep.verdict}"
      let total := tr.steps.foldl (fun s st => s+st.h) 0
      IO.println s!"affine length {showD total}"
      if let some last := rep.results.getLast? then
        IO.println s!"final position {[0,1,2].map fun (i : Fin 10) => showB (last.final i)}"
        IO.println s!"final momentum {[3,4,5].map fun (i : Fin 10) => showB (last.final i)}"
      if rep.verdict == .escaped then
        IO.println s!"direction (binary32, unnormalized) {(List.finRange 3).map fun i => showD (obs.direction i)}"
        IO.println s!"redshift (binary32) {showD obs.redshift}"
        IO.println "  angle error ≤ 1e-6 rad, redshift relative error ≤ 1e-6"
      return 0
  | _ => IO.println usage; return 2
