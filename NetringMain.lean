/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual
import Netring

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Netring


-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

/--
Extract the marked exercises and example code.
-/
partial def buildExercises (mode : Mode) (cfg : Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode
    | pure ()
  let code := (← part text |>.run {}).snd
  let dest := cfg.destination / "example-code"
  let some mainDir := mainFileName.parent
    | throw <| IO.userError "Can't find directory of `TextbookTemplateMain.lean`"

  IO.FS.createDirAll <| dest
  for ⟨fn, f⟩ in code do
    -- Make sure the path is relative to that of this one
    if let some fn' := fn.dropPrefix? mainDir.toString then
      let fn' := (fn'.dropWhile (· ∈ System.FilePath.pathSeparators)).copy
      let fn := dest / fn'
      if let some parent := fn.parent then IO.FS.createDirAll parent
      if (← fn.pathExists) then IO.FS.removeFile fn
      IO.FS.writeFile fn f
    else
      reportError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."

where
  part : Part Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
            let prior := prior.getD ""
            some (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
          let prior := prior.getD ""
          some (code.trimAsciiEnd.copy ++ "\n" ++ prior)

      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()


def saveForPreserving (toBeNuked : System.FilePath) (filenamesForPreservation : List String) : IO (Array (String × ByteArray)) := do
  if !(← toBeNuked.pathExists) then
    return #[]
  let mut saved: Array (String × ByteArray) := #[]
  for path in ← toBeNuked.walkDir do
    if let some name := path.fileName then
      if filenamesForPreservation.contains name && !(← path.isDir) then
        saved := saved.push (name, ← IO.FS.readBinFile path)
  return saved

def restorePreserved (parent : System.FilePath) (saved : Array (String × ByteArray)) : IO Unit := do
  IO.FS.createDirAll parent
  for (name, contents) in saved do
    IO.FS.writeBinFile (parent / name) contents

def outputDir : String := "docs"
def preserve : List String := ["CNAME"]

def clearWithPreservationList (fileToClear : System.FilePath) (toBePreserved : List String) : IO Unit := do
  let preserved ← saveForPreserving fileToClear toBePreserved
  if ← fileToClear.pathExists then
    IO.FS.removeDirAll fileToClear
  restorePreserved fileToClear preserved

def formatOutputForGithubPages (mode : Mode) (config : Config) (_s : TraverseState) (_t : Part Manual) : BuildLogT IO Unit := do

  -- Exit without doing anything if the project is being run weirdly
  let .multi := mode
    | pure ()

  clearWithPreservationList outputDir preserve

  let src := config.destination / "html-multi"
  Verso.FS.copyRecursively src outputDir

  IO.FS.removeDirAll config.destination



open Verso.Output Html in
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 5
  -- Copy the stylesheet into the output and link it from every page's `<head>`
  extraFilesHtml := [("custom_css", "custom_css"), ("assets", "assets")]
  extraHead := #[
    {{<link rel="stylesheet" href="custom_css/dark_mode.css"/>}},
    {{<link rel="stylesheet" href="custom_css/image_sizing.css"/>}}
  ]

theorem defaultDestination : config.destination.fileName = some "_out" := by native_decide

theorem noFileNameClashes :
  ∃ dest_isSome : config.destination.fileName.isSome = true,
    Option.get config.destination.fileName dest_isSome ∉ [outputDir] ++ preserve
  := by

  have h : config.destination.fileName.isSome = true := by
    simp [defaultDestination]

  exists h

  intro bad

  simp [defaultDestination] at bad

  cases bad with
  | inl s =>
    change "_out" = "docs" at s
    contradiction
  | inr x =>
    change "_out" ∈ ["CNAME"] at x
    contradiction

def main := manualMain (%doc Netring) (extraSteps := [buildExercises, formatOutputForGithubPages]) (config := config)
