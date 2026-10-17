/-
  Minimal executable entry point for the Civ6 optimality-certificate project.

  This file deliberately contains no game rules: it only proves that the
  project-local Lean 4.25.0 toolchain can elaborate and compile a program that
  imports the project root module `Civ6Verify`.
-/
import Civ6Verify

open Civ6Verify

def main : IO Unit := do
  IO.println "civ6-lean4: toolchain build OK"
  IO.println s!"Lean toolchain: {Lean.versionString}"
  IO.println s!"internal turn clock: t=0 is the initial state, t={tickExample} is one resolution later"
