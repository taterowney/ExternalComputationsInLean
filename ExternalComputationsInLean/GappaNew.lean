import ExternalComputationsInLean.Command
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

set_option linter.unusedVariables false set_option linter.unusedTactic false set_option linter.unreachableTactic false

injective external Gappa_input where
  x "+" y <== x + y
  x "-" y <== x - y
  x "*" y <== x * y
  x "/" y <== x / y
  x "^" y <== x ^ y
  "sqrt(" x ")" <== Real.sqrt x

  x "->" y <== x → y
  x "/\\" y <== x ∧ y
  x "\\/" y <== x ∨ y
  "not" x <== ¬ x

  "[" x "," y "]" <== Set.Icc x y
  x "in" y <== x ∈ y
  x "<=" y <== x ≤ y
  x "=" y <== x = y

-- noncomputable abbrev toReal (x) : Real := OfNat.ofNat x
macro "tac" : tactic => `(tactic| try decide; try simp_all <;> grind; try grind; try sorry)



surjective external Gappa_output (numberCast := Int.ofNat) where
  x "->" y   ==> x → y
  x "/\\" y  ==> x ∧ y
  x "\\/" y  ==> x ∨ y
  "not" x    ==> ¬ x
  "True"     ==> True
  "False"    ==> False
  "(" x ")"  ==> x
  "let" $n ":=" val "in" rest         ==> let n := val; rest
  "let" $n ":" ty ":=" val "in" rest  ==> let n:ty := val; rest
  "fun" $n "=>" rest                  ==> fun n => rest
  "fun" $n ":" ty "=>" rest           ==> fun n:ty => rest
  "-" x  ==> - x
  "_"    ==> _
  x y ==> (id ∘ x) y

  "Reals.Rdefinitions.R"                    ==> ℝ
  "Gappa.Gappa_pred_bnd.Float1" x           ==> (IntCast.intCast x : Real)
  "Gappa.Gappa_definitions.Float2" x y         ==> (IntCast.intCast x : Real) * ((2:Real) ^ (y:Int))
  "Gappa.Gappa_definitions.makepairF" x y   ==> Set.Icc x y
  "Gappa.Gappa_definitions.BND" x y         ==> x ∈ y
  "Reals.Rdefinitions.Rle" x y              ==> x ≤ y
  "Reals.Rdefinitions.Rplus" x y            ==> x + y
  "Reals.Rdefinitions.Rsub" x y             ==> x - y
  "Reals.Rdefinitions.Rmult" x y            ==> x * y
  "Reals.Rdefinitions.Rdiv" x y             ==> x / y
  "Reals.R_sqrt.sqrt" x                     ==> Real.sqrt x

  "Gappa.Gappa_pred_bnd.constant1" a b c          ==> by tac
  "Gappa.Gappa_tree.simplify" a         ==> by tac
  "Gappa.Gappa_pred_bnd.sqrtG" a b c d e          ==> by tac
  "Gappa.Gappa_pred_bnd.add" a b c d e f g h      ==> by tac
  "Gappa.Gappa_pred_bnd.mul_pp" a b c d e f g h   ==> by tac
  "Gappa.Gappa_pred_bnd.div_pp" a b c d e f g h   ==> by tac



partial def preprocess (s : String) : IO String :=
  -- let escaped_comments := s.replace "(*" "(*\"" |>.replace "*)" "\"*)"
  let escaped_comments := s.replace "(*" "/-" |>.replace "*)" "-/"
  let rec loop (input : String) (acc : String := "") : String :=
    if input = "" then acc else
    if input.dropWhile (· == ' ') |>.startsWith "Gappa.Gappa_tree.simplify" then
      loop (input.dropWhile (· != '\n') |>.drop 1) (acc ++ "Gappa.Gappa_tree.simplify _ in ")
    else
      let line := input.takeWhile (· != '\n')
      loop (input.dropWhile (· != '\n') |>.drop 1) (acc ++ line ++ "\n")
  let escaped := loop escaped_comments
  IO.Process.run {
    cmd := "python3",
    args := #[s!"/Users/trowney/Desktop/Code/gappa/gappa/preprocess.py", escaped],
    stdin := .piped,
    stdout := .piped,
    stderr := .piped
  }

open Lean Meta Elab Term Command Tactic in
elab "gappa" : tactic => do
  let goal ← getMainGoal
  let typ ← instantiateMVars (← goal.getType)
  logInfo m!"Current goal: {typ}"
  let formatted ← toExternal `Gappa_input typ
  logInfo m!"{formatted}"
  IO.FS.writeFile "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g" s!"\{{formatted}}"
  let res ← IO.Process.run {
    cmd := "/Users/trowney/Desktop/Code/gappa/gappa/src/gappa",
    args := #[s!"-Bcoq-lambda", "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g"],
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  let input ← preprocess res
  logInfo m!"Gappa output after preprocessing: {input}"
  let proof ← processExternal `Gappa_output input
  Meta.check proof
  logInfo m!"Parsed proof: {proof}"
  logInfo m!"Proof type: {← inferType proof}"
  logInfo m!"Goal type: {typ}"
  let proof ← Meta.whnf proof
  let proof ← Core.betaReduce proof

  let newhyp : Hypothesis := {
    userName := `h_gappa,
    type := ← Core.betaReduce (← Meta.whnf (← inferType proof)),
    value := proof
  }
  let ⟨ids, new⟩ ← goal.assertHypotheses #[newhyp]
  replaceMainGoal [new]

  let tac_stx : TSyntax `tactic ← `(tactic| norm_num at * )
  Lean.Elab.Tactic.evalTactic tac_stx

  let tac_stx : TSyntax `tactic ← `(tactic| try grind )
  Lean.Elab.Tactic.evalTactic tac_stx





-- example : √2 * 1000 ≤ 1415 := by
--   gappa



-- open Lean Meta in
-- #eval do
--   let expr ← processExternal `Gappa_output "let f1 := Gappa.Gappa_definitions.Float2 (1415) (0) in
-- 0"
--   logInfo m!"Elaborated expression: {expr}"
