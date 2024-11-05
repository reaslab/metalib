import Lean

open Lean Elab Meta Parser PrettyPrinter Tactic

def localDeclToBinder : LocalDecl → MetaM (TSyntax ``Term.bracketedBinder)
  | .cdecl _ _ name type bi _ => do
    let type ← delab (← instantiateMVars type)
    match bi with
    | .default => `(bracketedBinder| ($(mkIdent name) : $type))
    | .implicit => `(bracketedBinder| {$(mkIdent name) : $type})
    | .instImplicit => `(bracketedBinder| [$type])
    | .strictImplicit => `(bracketedBinder| ⦃$(mkIdent name) : $type⦄)
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

def goalToDeclSig (goal : MVarId) : MetaM (TSyntax ``Command.declSig) :=
  withEnableInfoTree false <| goal.withContext do
    let binders ← contextToBinders
    let type ← goal.getType
    let type ← delab (← instantiateMVars type)
    `(declSig| $[$binders]* : $type)
