/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean Elab Meta

namespace Lean.Elab.Tactic.TacticM

def runWithInfoBefore {α : Type} (ci : ContextInfo) (ti : TacticInfo) (x : TacticM α) : IO α :=
  { ci with mctx := ti.mctxBefore }.runMetaM {} <|
    x { elaborator := .anonymous, recover := false } |>.run' { goals := ti.goalsBefore }
    |>.run'

def runWithInfoAfter {α : Type} (ci : ContextInfo) (ti : TacticInfo) (x : TacticM α) : IO α :=
  { ci with mctx := ti.mctxAfter }.runMetaM {} <|
    x { elaborator := .anonymous, recover := false } |>.run' { goals := ti.goalsAfter }
    |>.run'

def runWithInfo {α : Type} (useAfter : Bool) : ContextInfo → TacticInfo → TacticM α → IO α :=
  if useAfter then runWithInfoAfter else runWithInfoBefore

end Lean.Elab.Tactic.TacticM
