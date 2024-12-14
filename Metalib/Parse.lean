/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean Meta Parser Elab Term Command Tactic

section
variable {m : Type _ → Type _} [Monad m] [MonadResolveName m]

def runParserFn (fn : ParserFn) (env : Environment) (input : String) (filename : String := "") : m ParserState := do
  let ictx := mkInputContext input filename
  let pmctx := {
    env,
    options := .empty,
    currNamespace := ← getCurrNamespace,
    openDecls := ← getOpenDecls,
  }
  let result := fn.run ictx pmctx (getTokenTable env) (mkParserState input)
  return result

variable [MonadEnv m] [MonadError m]

def runParserFnM (fn : ParserFn) (input : String) (filename : String := "") : m Syntax := do
  let result ← runParserFn fn (← getEnv) input filename
  if let some error := result.errorMsg then
    throwError error.toString
  return result.stxStack.back

def parseTerm : String → m Syntax := runParserFnM termParser.fn

def parseGoal (vars : Array (Name × String)) (name : Name) (type : String) : TermElabM MVarId :=
  withLocalDeclsD (vars.map fun (n, t) => (n, fun _ => do elabType (← parseTerm t))) fun _ => do
    let type ← elabType (← parseTerm type)
    let mvar ← mkFreshExprMVar type .synthetic (userName := name)
    pure mvar.mvarId!
end
