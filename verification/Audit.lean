module

import BlackHole
import Lean.Util.CollectAxioms

set_option warningAsError true

open Lean Elab Command

set_option maxHeartbeats 2000000 in
run_cmd do
  let env ← getEnv
  unless (env.find? `BlackHole.KerrField.ricci_zero).isSome do
    throwError "The complete Kerr vacuum theorem was not imported."
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    if (`BlackHole).isPrefixOf name then
      declarations := declarations+1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
  if declarations == 0 then
    throwError "No project declarations were audited."
  logInfo m!"Audited {declarations} project declarations; only standard axioms."
