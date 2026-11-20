import PathosProofs
/-!
Prints, for the theorems of the modules `PathosProofs.*` and of the
generated `MiniProofs`, `MiniCacheSem`, `MiniEmbed` and `MiniCtors`, the axioms they rest on: one line `axiom <name> assumption|declaration` for
each (an assumption is an axiom whose type is a proposition), a line
`theorems <count>`, and a line `prop <name>` for each axiom of the Lean of
the checker or of Aeneas's library that is a proposition.
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
      if ((`PathosProofs).isPrefixOf m && m != `PathosProofs.Trusted) || m == `MiniProofs ||
          m == `MiniCacheSem || m == `MiniEmbed ||
          m == `MiniCtors then
        if ci matches .thmInfo _ then
          count := count + 1
          let used ← liftCoreM (collectAxioms n)
          for a in used do
            axioms := axioms.insert a
  IO.println s!"theorems {count}"
  -- Whether an axiom's type is a proposition: an assumption, as against a
  -- declaration of a type or a function.
  let isProp (a : Name) : CommandElabM Bool := do
    match env.find? a with
    | some ci => liftTermElabM (Meta.isProp ci.type)
    | none => pure false
  for a in axioms.toList.mergeSort (fun x y => x.toString ≤ y.toString) do
    let kind := if (← isProp a) then "assumption" else "declaration"
    IO.println s!"axiom {a} {kind}"
  -- The axioms of the Lean of the checker and of Aeneas's library that are
  -- propositions, whether in use or not.
  for (n, ci) in env.constants.toList do
    if ci matches .axiomInfo _ then
      match env.getModuleIdxFor? n with
      | none => pure ()
      | some idx =>
        let m := names[idx.toNat]!
        if (`MiniChecker).isPrefixOf m || (`Aeneas).isPrefixOf m then
          if (← isProp n) then
            IO.println s!"prop {n}"
