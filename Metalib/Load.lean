/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean

open Lean Elab Parser System Frontend

def handleHeader (header : Syntax) (messages : MessageLog) (inputCtx : InputContext) : IO Command.State := do
  initSearchPath (← findSysroot)
  let (env, messages) ← processHeader (leakEnv := true) header .empty messages inputCtx
  return Command.mkState env messages

def loadFrontend (inputCtx : InputContext) (initState : Syntax → MessageLog → InputContext → IO Command.State := handleHeader) : IO (Context × State) := do
  let (header, parserState, messages) ← parseHeader inputCtx
  let commandState ← initState header messages inputCtx
  return ({ inputCtx }, { commandState, parserState, cmdPos := parserState.pos, commands := #[] })

def loadFile (path : FilePath) : IO (Context × State) := do
  let input ← IO.FS.readFile path
  let inputCtx := mkInputContext input path.toString
  loadFrontend inputCtx

def withFile {α : Type _} (path : FilePath) (m : FrontendM α) : IO (α × State) := do
  let (context, state) ← loadFile path
  m context |>.run state