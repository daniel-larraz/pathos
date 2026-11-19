import PathosProofs
/-!
Prints, for the theorems of the modules `PathosProofs.*`, the axioms they
rest on: one line `axiom <name>` for each, and a line `theorems <count>`.
`scripts/proofs-axioms` runs this and compares the names with
`proofs/axioms-allowed.txt`.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut axioms : NameSet := {}
  let mut count := 0
  let names := env.header.moduleNames
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let m := names[idx.toNat]!
      if (`PathosProofs).isPrefixOf m && m != `PathosProofs.Trusted then
        if ci matches .thmInfo _ then
          count := count + 1
          let used ← liftCoreM (collectAxioms n)
          for a in used do
            axioms := axioms.insert a
  IO.println s!"theorems {count}"
  for a in axioms.toList.map toString |>.mergeSort do
    IO.println s!"axiom {a}"
