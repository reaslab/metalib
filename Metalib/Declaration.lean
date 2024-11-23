/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean Elab Meta Parser PrettyPrinter Tactic

def localDeclToBinder : LocalDecl → MetaM (TSyntax ``Term.bracketedBinder)
  | .cdecl _ _ name type bi _ => do
    let ident := mkIdent name
    let type ← delab (← instantiateMVars type)
    match bi with
    | .default => `(bracketedBinder| ($ident : $type))
    | .implicit => `(bracketedBinder| {$ident : $type})
    | .instImplicit => `(bracketedBinder| [$type])
    | .strictImplicit => `(bracketedBinder| ⦃$ident : $type⦄)
  | .ldecl .. => pure ⟨ .missing ⟩  -- FIXME: handle let-bindings?

def contextToBinders : MetaM (TSyntaxArray ``Term.bracketedBinder) := do
  let lctx ← getLCtx
  let lctx : LocalContext := lctx.sanitizeNames.run' { options := ← getOptions }
  let mut binders := Array.mkEmpty lctx.size
  for ldecl in lctx do
    if ldecl.isImplementationDetail then
      continue
    binders := binders.push (← localDeclToBinder ldecl)
  return binders

def goalToDecl (goal : MVarId) (name : Name) : MetaM (TSyntax `command) :=
  withEnableInfoTree false <| goal.withContext do
    let binders ← contextToBinders
    let type ← instantiateMVars (← goal.getType)
    let typeTerm ← delab type
    let isProp := (← inferType type).isProp
    let ident := mkIdent name
    if isProp then
      `(theorem $ident $[$binders]* : $typeTerm := sorry)
    else
      `(def $ident $[$binders]* : $typeTerm := sorry)
