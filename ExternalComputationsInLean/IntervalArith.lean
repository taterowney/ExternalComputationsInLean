import ExternalComputationsInLean.Elaborator

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


open Lean Meta Tactic Elab Meta Term Tactic Expr Lean.Meta.Tactic.TryThis
open Qq


def elaborator_float : Expr → MetaM String :=
  let equality := py_elab ((x : Float32) = (y : Float32)) ==> print_equality

  let real := py_elab ((x : Float32)) ==> print_float

  let nat := py_elab ((n : ℕ)) ==> print_nat

  let addition := py_elab ((a : Float32) + (b : Float32)) ==> fun e => do
    return s!"{e.2[0]!} + {e.2[1]!}"

  let subtraction := py_elab ((x : Float32) - (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} - {e.2[1]!}"

  let multiplication := py_elab ((x : Float32) * (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} * {e.2[1]!}"

  let le := py_elab ((x : Float32) ≤ (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} <= {e.2[1]!}"

  let lt := py_elab ((x : Float32) < (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} < {e.2[1]!}"

  let ge := py_elab ((x : Float32) ≥ (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} >= {e.2[1]!}"

  let gt := py_elab ((x : Float32) > (y : Float32)) ==> fun e => do
    return s!"{e.2[0]!} > {e.2[1]!}"

  doPythonElaboration [equality, addition, subtraction, multiplication, real, nat, le, lt, ge, gt]




def elaborator : Expr → MetaM String :=
  let equality := py_elab ((x : ℝ) = (y : ℝ)) ==> print_equality

  let real := py_elab ((x : ℝ)) ==> print_real

  let nat := py_elab ((n : ℕ)) ==> print_nat

  let int := py_elab ((n : Int)) ==> print_int

  let neg_int := py_elab (-(n : Int)) ==> fun e => do
    return s!"-{e.2[0]!}"

  let addition := py_elab ((x : ℝ) + (y : ℝ)) ==> fun e => do
    return s!"{e.2[0]!} + {e.2[1]!}"

  let subtraction := py_elab ((x : ℝ) - (y : ℝ)) ==> fun e => do
    return s!"{e.2[0]!} - {e.2[1]!}"

  let multiplication := py_elab ((x : ℝ) * (y : ℝ)) ==> fun e => do
    return s!"{e.2[0]!} * {e.2[1]!}"

  let exponentiation := py_elab ((x : ℝ) ^ (y : ℤ)) ==> fun e => do
    return s!"{e.2[0]!} ^ {e.2[1]!}"

  let division := py_elab ((x : ℝ) / (y : ℝ)) ==> fun e => do
    return s!"({e.2[0]!} / {e.2[1]!})"

  let le := py_elab ((x : Real) ≤ (y : Real)) ==> fun e => do
    return s!"{e.2[0]!} <= {e.2[1]!}"

  let lt := py_elab ((x : Real) < (y : Real)) ==> fun e => do
    return s!"{e.2[0]!} < {e.2[1]!}"

  let ge := py_elab ((x : Real) ≥ (y : Real)) ==> fun e => do
    return s!"{e.2[0]!} >= {e.2[1]!}"

  let gt := py_elab ((x : Real) > (y : Real)) ==> fun e => do
    return s!"{e.2[0]!} > {e.2[1]!}"

  let implies := py_elab (x → y) ==> fun e => do
    return s!"({e.2[0]!}) -> ({e.2[1]!})"

  let and := py_elab (x ∧ y) ==> fun e => do
    return s!"({e.2[0]!}) /\\ ({e.2[1]!})"

  -- let icc := py_elab ((x : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ)) ==> fun e => do
  --   return s!"{e.2[0]!} in [{e.2[1]!}, {e.2[2]!}]"

  -- let icc := py_elab (Set.Icc 1 2) ==> fun e => do
  --   return s!"hooray"

  let sqrt := py_elab (Real.sqrt (x : ℝ)) ==> fun e => do
    return s!"sqrt({e.2[0]!})"

  doPythonElaboration [equality, addition, subtraction, multiplication, division, exponentiation, le, lt, ge, gt, implies, and, sqrt, real, nat, neg_int, int]

#check Real.sqrt

elab "#test_elab" c:term : command => do
  withoutModifyingEnv <| Elab.Command.runTermElabM fun _ => Term.withDeclName `_test_elab do
    let mut e ← Term.elabTerm c (none)
    e ← instantiateMVars e

    let formatted ← elaborator e
    logInfo m!"{formatted}"
  return


-- elab "#gappa " c:term : command => do
--   withoutModifyingEnv <| Elab.Command.runTermElabM fun _ => Term.withDeclName `_gappa do
--     let mut e ← Term.elabTerm c (some (q(Prop)))
--     e ← instantiateMVars e

--     let formatted ← elaborator e
--     IO.FS.writeFile "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g" s!"\{{formatted}}"
--     let res ← IO.Process.run {
--       cmd := "/Users/trowney/Desktop/Code/gappa/gappa/src/gappa",
--       args := #[s!"-Bcoq", "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g"],
--       stdin := .piped,
--       stdout := .piped,
--       stderr := .piped
--     }
--     logInfo m!"{res}"
--   return

elab "gappa" : tactic => do
  let goal ← getMainGoal
  let formatted ← elaborator (← goal.getType')
  IO.FS.writeFile "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g" s!"\{{formatted}}"
  let res ← IO.Process.run {
    cmd := "/Users/trowney/Desktop/Code/gappa/gappa/src/gappa",
    args := #[s!"-Bcoq-lambda", "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g"],
    stdin := .piped,
    stdout := .piped,
    stderr := .piped
  }
  logInfo m!"{res}"
  admitGoal goal
  return



variable (y : ℝ)

example : y >= 0 ∧ y <= 3 → √y * 1024 <= 1775 := by
  gappa

def test := fun (x: Nat) => let n := 5; n + x
