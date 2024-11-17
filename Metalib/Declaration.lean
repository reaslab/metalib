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

def contextToBinders (lctx : LocalContext) : MetaM (TSyntaxArray ``Term.bracketedBinder) := do
  let lctx : LocalContext := lctx.sanitizeNames.run' { options := ← getOptions }
  let mut binders := Array.mkEmpty lctx.size
  for ldecl in lctx do
    if ldecl.isImplementationDetail then
      continue
    binders := binders.push (← localDeclToBinder ldecl)
  return binders

/-- Construct a declaration from `goal1`. For now one should explicitly
check the existence of `goal1` and `goal2`.  -/
def goalToDecl (goal : MVarId) (name : Name) : MetaM (TSyntax `command) :=
  withEnableInfoTree false <| goal.withContext do
    let lctx ← getLCtx
    let binders ← contextToBinders lctx
    let type ← instantiateMVars (← goal.getType)
    let typeTerm ← delab type
    let isProp := (← inferType type).isProp
    let ident := mkIdent name
    if isProp then
      `(theorem $ident $[$binders]* : $typeTerm := sorry)
    else
      `(def $ident $[$binders]* : $typeTerm := sorry)

/-- Construct a declaration from `goal1` and `goal2`. For now one should explicitly
check the existence of `goal1` and `goal2`.  -/
def goal2ToDecl (goal1 goal2 : MVarId) (name : Name) : MetaM (TSyntax `command) :=
  withEnableInfoTree false <| goal1.withContext do
    let lctx ← getLCtx
    let type2 ← instantiateMVars (← goal2.getType)
    -- add `hg2` of the goal2 type to the local context of goal1 for proof
    let lctx := lctx.mkLocalDecl (← mkFreshFVarId) `hg2 type2
    let binders ← contextToBinders lctx
    let type ← instantiateMVars (← goal1.getType)
    let typeTerm ← delab type
    let isProp := (← inferType type).isProp
    let ident := mkIdent name
    if isProp then
      `(theorem $ident $[$binders]* : $typeTerm := sorry)
    else
      `(def $ident $[$binders]* : $typeTerm := sorry)
