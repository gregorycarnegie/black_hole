module

public import BlackHole.WgslGeodesic
public import BlackHole.WgslAtan2
public import BlackHole.WgslPlasma
public import BlackHole.WgslAddKerr
public import BlackHole.WgslAtan2Program
public import BlackHole.WgslSinCosProgram
public import BlackHole.WgslTransferProgram

/-! Translation-validation fixture for the straight-line kernels (obligation
F3).

`fixtures/kernels.sexp` records, one per line, the name and expression tree of
each modeled kernel output. `fixture_eq` checks in the kernel that the file
denotes exactly the `PExpr` programs whose error bounds are proved
(`WgslGeodesic.rhs`, `WgslAtan2.polyE`). The Rust test
`tests/translation.rs` parses the same file and compares it with the naga IR
that the front end produces from `geodesic.wesl`, modulo the reassociation and
commutation of sums and products that the error bounds already allow.

Grammar: `(in i)`, `(c num den)`, `(add a b)`, `(sub a b)`, `(mul a b)`,
`(neg a)`, `(divc a num den)`. Regenerate both fixture files with
`lake env lean --run KernelFixtureGen.lean`; `fixtures/naga-raw.sexp` (naga's
own trees, read by `nagaFixture`) with `UPDATE_NAGA_RAW=1 cargo test --release
--test translation`. -/

@[expose] public section

namespace BlackHole.KernelFixture
open WgslPoly PExpr

/-- The kernel outputs the fixture records, in order. -/
def kernels : List (String × PExpr) :=
  [("geodesic_rhs", WgslGeodesic.rhs 0), ("geodesic_rhs", WgslGeodesic.rhs 1),
    ("geodesic_rhs", WgslGeodesic.rhs 2), ("geodesic_rhs", WgslGeodesic.rhs 3),
    ("geodesic_rhs", WgslGeodesic.rhs 4), ("geodesic_rhs", WgslGeodesic.rhs 5),
    ("geodesic_rhs", WgslGeodesic.rhs 6), ("geodesic_rhs", WgslGeodesic.rhs 7),
    ("geodesic_rhs", WgslGeodesic.rhs 8), ("geodesic_rhs", WgslGeodesic.rhs 9),
    ("geodesic_rhs", WgslGeodesic.rhs 10), ("atan_poly", WgslAtan2.polyE)]

def sexp : PExpr → String
  | input i => s!"(in {i})"
  | const c => s!"(c {c.num} {c.den})"
  | add a b => s!"(add {sexp a} {sexp b})"
  | sub a b => s!"(sub {sexp a} {sexp b})"
  | mul a b => s!"(mul {sexp a} {sexp b})"
  | neg a => s!"(neg {sexp a})"
  | divc a c => s!"(divc {sexp a} {c.num} {c.den})"

def render : String := String.intercalate "\n" (kernels.map fun (n,e) => n ++ " " ++ sexp e) ++ "\n"

private meta def fixtureText : String := include_str ".."/"fixtures"/"kernels.sexp"

private meta def ratTerm (n d : String) : Lean.MacroM Lean.Term := do
  let some d := d.toNat? | Lean.Macro.throwError s!"invalid denominator {d}"
  if n.startsWith "-" then
    let some a := (n.drop 1).toString.toNat? | Lean.Macro.throwError s!"invalid numerator {n}"
    unless 0 < a do Lean.Macro.throwError "negative zero numerator"
    `(mkRat (Int.negSucc $(Lean.quote (a-1))) $(Lean.quote d))
  else
    let some a := n.toNat? | Lean.Macro.throwError s!"invalid numerator {n}"
    `(mkRat (Int.ofNat $(Lean.quote a)) $(Lean.quote d))

private meta partial def parse : List String → Lean.MacroM (Lean.Term × List String)
  | "(" :: "in" :: i :: ")" :: rest => do
    let some i := i.toNat? | Lean.Macro.throwError s!"invalid input {i}"
    return (← `(PExpr.input $(Lean.quote i)), rest)
  | "(" :: "c" :: n :: d :: ")" :: rest => do
    return (← `(PExpr.const $(← ratTerm n d)), rest)
  | "(" :: "neg" :: rest => do
    let (a, rest) ← parse rest
    let ")" :: rest := rest | Lean.Macro.throwError "expected )"
    return (← `(PExpr.neg $a), rest)
  | "(" :: "divc" :: rest => do
    let (a, rest) ← parse rest
    let n :: d :: ")" :: rest := rest | Lean.Macro.throwError "expected divisor"
    return (← `(PExpr.divc $a $(← ratTerm n d)), rest)
  | "(" :: op :: rest => do
    let (a, rest) ← parse rest
    let (b, rest) ← parse rest
    let ")" :: rest := rest | Lean.Macro.throwError "expected )"
    match op with
    | "add" => return (← `(PExpr.add $a $b), rest)
    | "sub" => return (← `(PExpr.sub $a $b), rest)
    | "mul" => return (← `(PExpr.mul $a $b), rest)
    | _ => Lean.Macro.throwError s!"unknown operation {op}"
  | _ => Lean.Macro.throwError "malformed expression"

private meta def tokens (row : String) : List String :=
  (((row.replace "(" " ( ").replace ")" " ) ").splitOn " ").filter fun t => t ≠ ""

macro "kernel_fixture" : term => do
  let rows := (fixtureText.trimAscii.toString.splitOn "\n").map (·.trimAscii.toString)
  let entries ← rows.toArray.mapM fun row => do
    let name :: toks := tokens row | Lean.Macro.throwError "empty row"
    let (e, rest) ← parse toks
    unless rest.isEmpty do Lean.Macro.throwError s!"trailing tokens in {name}"
    `(Prod.mk $(Lean.quote name) $e)
  `([$entries,*])

def fixture : List (String × PExpr) := kernel_fixture

/-- The committed fixture is exactly the modeled kernels. -/
theorem fixture_eq : fixture = kernels := by decide +kernel

/-! ### Kernels with branches and builtins

`fixtures/kernels-branching.sexp` uses the `GExpr` grammar: the operations
above plus `(div a b)`, `(max a b)`, `(min a b)`, unary `(sqrt a)`, `(abs a)`,
`(invsqrt a)`, `(exp a)`, `(exp2 a)`, `(log a)`, `(log2 a)`, `(sinS a)`,
`(cosS a)`, `(inh f a)`, `(tanh f a)`, `(lt c num den a b)`,
`(lt2 a b x y)`, `(scale k a)` for `2^k * a`, `(round a)` and
`(qsel j k s c)`. -/

/-- Matrix entries in WGSL storage order: column by column. -/
def columns {α : Type} (f : Fin 4 → Fin 4 → α) : List α :=
  (List.finRange 4).flatMap fun c => (List.finRange 4).map fun r => f r c

/-- `add_kerr`'s outputs in the order of the `Metric` struct: `g`, `inv`,
`dx`, `dy`, `dz`, `clearance` (the `valid` flag is not modeled here). -/
def addKerrOutputs : List WgslAddKerr.Output :=
  columns .metric ++ columns .inverse ++
    (List.finRange 3).flatMap (fun e => columns (.derivative e)) ++ [.clearance]

/-- A model written with `let` slots (`WgslLets`): its slots under
`name:let`, then its outputs under `name`. -/
def slotProgram (name : String) (slots outputs : List WgslExpr.GExpr) :
    List (String × WgslExpr.GExpr) :=
  slots.map (fun e => (name ++ ":let", e)) ++ outputs.map fun e => (name, e)

/-- The twelve `Plasma` fields over the plasma slots. -/
def plasmaOutputs : List WgslExpr.GExpr := List.ofFn WgslPlasma.plasmaOut

open WgslExpr in
/-- The branching kernel outputs the fixture records, in order. `tonemap` is
recorded once per channel; `spatial_unit` reads `v` from inputs 100–102. -/
def branching : List (String × WgslExpr.GExpr) :=
  [("tonemap", WgslPlasma.tonemap), ("tonemap", WgslPlasma.tonemap),
    ("tonemap", WgslPlasma.tonemap),
    ("heatmap_color", WgslPlasma.heatmap 0), ("heatmap_color", WgslPlasma.heatmap 1),
    ("heatmap_color", WgslPlasma.heatmap 2),
    ("polarization_color", WgslPlasma.polarizationHue 0),
    ("polarization_color", WgslPlasma.polarizationHue 1),
    ("polarization_color", WgslPlasma.polarizationHue 2),
    ("spatial_unit", WgslScreen.spatialUnit (fun j => GExpr.input (100+j)) 0),
    ("spatial_unit", WgslScreen.spatialUnit (fun j => GExpr.input (100+j)) 1),
    ("spatial_unit", WgslScreen.spatialUnit (fun j => GExpr.input (100+j)) 2),
    ("spin_scale", WgslAddKerr.spinScale 0), ("spin_scale", WgslAddKerr.spinScale 1),
    ("spin_scale", WgslAddKerr.spinScale 2)] ++
  addKerrOutputs.map (fun o => ("add_kerr", WgslAddKerr.program o)) ++
  slotProgram "screen_frame" WgslScreen.frameLets
    ((List.finRange 3).flatMap fun col => (List.finRange 3).map fun i =>
      WgslLets.ref (WgslScreen.frameSlot col i)) ++
  slotProgram "sample_plasma.0" (WgslPlasma.plasmaLets 0) plasmaOutputs ++
  slotProgram "sample_plasma.1" (WgslPlasma.plasmaLets 1) plasmaOutputs ++
  slotProgram "sample_plasma.2" (WgslPlasma.plasmaLets 2) plasmaOutputs ++
  slotProgram "sample_plasma.3" (WgslPlasma.plasmaLets 3) plasmaOutputs ++
  slotProgram "atan2_arith" WgslAtan2Program.atan2Lets [WgslAtan2Program.atan2Out] ++
  slotProgram "kerr_radius" WgslKerrProgram.kerrLets [WgslKerrProgram.kerrOut] ++
  slotProgram "sincos" WgslSinCosProgram.sincosLets
    [WgslSinCosProgram.sincosOut false, WgslSinCosProgram.sincosOut true] ++
  slotProgram "transfer_phi" WgslTransferProgram.phiProgLets
    [WgslTransferProgram.phiProgOut false, WgslTransferProgram.phiProgOut true] ++
  slotProgram "faraday_rotation" WgslTransferProgram.faradayLets
    ((List.finRange 3).flatMap fun col => (List.finRange 3).map fun row =>
      WgslTransferProgram.faradayOut col row) ++
  slotProgram "polarized_cell" WgslTransferProgram.cellLets
    (List.ofFn WgslTransferProgram.cellOut)

def gsexp : WgslExpr.GExpr → String
  | .input i => s!"(in {i})"
  | .const c => s!"(c {c.num} {c.den})"
  | .add a b => s!"(add {gsexp a} {gsexp b})"
  | .sub a b => s!"(sub {gsexp a} {gsexp b})"
  | .mul a b => s!"(mul {gsexp a} {gsexp b})"
  | .div a b => s!"(div {gsexp a} {gsexp b})"
  | .max a b => s!"(max {gsexp a} {gsexp b})"
  | .min a b => s!"(min {gsexp a} {gsexp b})"
  | .neg a => s!"(neg {gsexp a})"
  | .sqrt a => s!"(sqrt {gsexp a})"
  | .abs a => s!"(abs {gsexp a})"
  | .invsqrt a => s!"(invsqrt {gsexp a})"
  | .exp a => s!"(exp {gsexp a})"
  | .exp2 a => s!"(exp2 {gsexp a})"
  | .log a => s!"(log {gsexp a})"
  | .log2 a => s!"(log2 {gsexp a})"
  | .sinS a => s!"(sinS {gsexp a})"
  | .cosS a => s!"(cosS {gsexp a})"
  | .inh f a => s!"(inh {gsexp f} {gsexp a})"
  | .tanh f a => s!"(tanh {gsexp f} {gsexp a})"
  | .lt c t a b => s!"(lt {gsexp c} {t.num} {t.den} {gsexp a} {gsexp b})"
  | .lt2 a b x y => s!"(lt2 {gsexp a} {gsexp b} {gsexp x} {gsexp y})"
  | .scale k a => s!"(scale {k} {gsexp a})"
  | .round a => s!"(round {gsexp a})"
  | .qsel j k a b => s!"(qsel {if j then 1 else 0} {gsexp k} {gsexp a} {gsexp b})"

def renderBranching : String :=
  String.intercalate "\n" (branching.map fun (n,e) => n ++ " " ++ gsexp e) ++ "\n"

private meta def branchingText : String := include_str ".."/"fixtures"/"kernels-branching.sexp"

private meta def intTerm (k : String) : Lean.MacroM Lean.Term := do
  if k.startsWith "-" then
    let some n := (k.drop 1).toString.toNat? | Lean.Macro.throwError s!"invalid integer {k}"
    unless 0 < n do Lean.Macro.throwError "negative zero"
    `(Int.negSucc $(Lean.quote (n-1)))
  else
    let some n := k.toNat? | Lean.Macro.throwError s!"invalid integer {k}"
    `(Int.ofNat $(Lean.quote n))

private meta partial def gparse : List String → Lean.MacroM (Lean.Term × List String)
  | "(" :: "in" :: i :: ")" :: rest => do
    let some i := i.toNat? | Lean.Macro.throwError s!"invalid input {i}"
    return (← `(WgslExpr.GExpr.input $(Lean.quote i)), rest)
  | "(" :: "c" :: n :: d :: ")" :: rest => do
    return (← `(WgslExpr.GExpr.const $(← ratTerm n d)), rest)
  | "(" :: "lt" :: rest => do
    let (c, rest) ← gparse rest
    let n :: d :: rest := rest | Lean.Macro.throwError "expected threshold"
    let (a, rest) ← gparse rest
    let (b, rest) ← gparse rest
    let ")" :: rest := rest | Lean.Macro.throwError "expected )"
    return (← `(WgslExpr.GExpr.lt $c $(← ratTerm n d) $a $b), rest)
  | "(" :: "qsel" :: j :: rest => do
    let (k, rest) ← gparse rest
    let (a, rest) ← gparse rest
    let (b, rest) ← gparse rest
    let ")" :: rest := rest | Lean.Macro.throwError "expected )"
    let jt ← match j with
      | "0" => `(false)
      | "1" => `(true)
      | _ => Lean.Macro.throwError s!"invalid component {j}"
    return (← `(WgslExpr.GExpr.qsel $jt $k $a $b), rest)
  | "(" :: "scale" :: k :: rest => do
    let (a, rest) ← gparse rest
    let ")" :: rest := rest | Lean.Macro.throwError "expected )"
    return (← `(WgslExpr.GExpr.scale $(← intTerm k) $a), rest)
  | "(" :: op :: rest => do
    let mut args : Array Lean.Term := #[]
    let mut rest := rest
    while rest.head? == some "(" do
      let (a, r) ← gparse rest
      args := args.push a
      rest := r
    let ")" :: rest' := rest | Lean.Macro.throwError "expected )"
    let ctor ← match op, args.size with
      | "add", 2 | "sub", 2 | "mul", 2 | "div", 2 | "max", 2 | "min", 2 | "inh", 2
      | "tanh", 2 | "neg", 1 | "sqrt", 1 | "abs", 1 | "invsqrt", 1 | "exp", 1 | "exp2", 1
      | "log", 1 | "log2", 1 | "sinS", 1 | "cosS", 1 | "round", 1 | "lt2", 4 =>
        pure (Lean.mkIdent (Lean.Name.mkStr `BlackHole.WgslExpr.GExpr op))
      | _, _ => Lean.Macro.throwError s!"unknown operation {op}/{args.size}"
    return (← `($ctor $args*), rest')
  | _ => Lean.Macro.throwError "malformed expression"

macro "branching_fixture" : term => do
  let rows := (branchingText.trimAscii.toString.splitOn "\n").map fun r => r.trimAscii.toString
  let entries ← rows.toArray.mapM fun row => do
    let name :: toks := tokens row | Lean.Macro.throwError "empty row"
    let (e, rest) ← gparse toks
    unless rest.isEmpty do Lean.Macro.throwError s!"trailing tokens in {name}"
    `(Prod.mk $(Lean.quote name) $e)
  `([$entries,*])

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
def branchingFixture : List (String × WgslExpr.GExpr) := branching_fixture

private meta def nagaText : String := include_str ".."/"fixtures"/"naga-raw.sexp"

/-- `fixtures/naga-raw.sexp`: naga's own trees for every compared kernel,
written by `tests/translation.rs`; `NagaFixture` checks them. -/
macro "naga_fixture" : term => do
  let rows := (nagaText.trimAscii.toString.splitOn "
").map fun r => r.trimAscii.toString
  let entries ← rows.toArray.mapM fun row => do
    let name :: toks := tokens row | Lean.Macro.throwError "empty row"
    let (e, rest) ← gparse toks
    unless rest.isEmpty do Lean.Macro.throwError s!"trailing tokens in {name}"
    `(Prod.mk $(Lean.quote name) $e)
  `([$entries,*])

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
def nagaFixture : List (String × WgslExpr.GExpr) := naga_fixture

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- The committed branching fixture is exactly the modeled kernels. -/
theorem branching_fixture_eq : branchingFixture = branching := by decide +kernel

end BlackHole.KernelFixture
