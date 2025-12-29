import ExternalComputationsInLean.LeanToExternal.Basic
import ExternalComputationsInLean.Utils.Pattern
open Lean Meta Elab Meta Term Expr Command

/-- Ensures that the names of the blanks in the syntax patterns and expression pattern are identical up to permutation, and that both are well-formed, etc. -/
def ensureConsistent (syntaxPats : Array (TSyntax `stx)) (exprPat : ExprPattern) : CommandElabM Unit := do
  return


syntax (name := externalPhrase) "external" stx+ "<==>" term : command

@[command_elab externalPhrase]
def externalPhraseImpl : CommandElab := fun stx => do
  let syntaxPats := stx.getArgs[1]!.getArgs.map (fun x => ⟨x⟩)
  let target : TSyntax `term := ⟨stx.getArgs[3]!⟩

  let (targetPat, variables) ← liftTermElabM <| target.toPattern none

  -- Ensure consistency between syntax patterns and expression pattern
  ensureConsistent syntaxPats targetPat

  declareExternal `externalcat syntaxPats targetPat variables


set_option pp.rawOnError true
external "zero" <==> 0
external "one" <==> 1
external z "+" y <==> (z:Nat) + y
-- external "succ" x <==> Nat.succ x
-- external "double" x <==> (2:Nat) * x
-- external "(" x ")" <==> x
#print «_aux_ExternalComputationsInLean_Main___elabRules_externalcat_+__1»

syntax (name := processExternalCmd) "process" term : term
@[term_elab processExternalCmd]
def processExternalCmdImpl : TermElab := fun stx _ => do
  let input : String := stx.getArgs[1]!.isStrLit?.get!
  let out ← processExternal `externalcat input
  return out


#eval process "one + one"




/-TODO:
- Fix problems with multiple blanks
- Check if extra stuff comes after successful match
- Full suppport for multiple categories
- Custom parsing functions (for stuff like numerals, etc.)
- Better error messages when metavariables can't be inferred fully
  - Assume numerals are Nats when type not explicitly specified
- Deal with metavar synthesis postponing if something doesn't work (for tactics etc)
- Could we skip the entire elaboration step by just looking at the SyntaxNodeKind?
- Backtracking (in parsing too) for type filtration?
-/
