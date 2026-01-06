import ExternalComputationsInLean.LeanToExternal.Basic
import ExternalComputationsInLean.Utils.Pattern
open Lean Meta Elab Meta Term Expr Command
open Qq




declare_syntax_cat externalDSLline
syntax (stx+) "<==>" term : externalDSLline

def lineParser : Parser.Parser :=
  Lean.Parser.many1Indent (Lean.Parser.categoryParser `externalDSLline 1)

/-- Declare an external DSL. Lines that follow describe equivalences between Lean types and external syntax.  -/
syntax (name := externalDSL) "external" ident "where" ppLine lineParser : command

@[command_elab externalDSL]
def externalPhraseImpl : CommandElab := fun stx => do
  let `(external $name where $lines:externalDSLline*) := stx | throwUnsupportedSyntax
  if lines.size == 0 then throwUnsupportedSyntax
  initializeExternalCategory name

  let name := name.getId
  for line in lines do
    match line.raw.getArgs.toList with
    | [syntaxPat, _, targetExpr] =>
      let syntaxPats := syntaxPat.getArgs.map .mk
      let target : TSyntax `term := ⟨targetExpr⟩
      declareExternal name syntaxPats target
    | _ => throwError m!"Unsupported external DSL line syntax: {line}"


syntax (name := processExternalCmd) "process" term : term
@[term_elab processExternalCmd]
def processExternalCmdImpl : TermElab := fun stx _ => do
  let input : String := stx.getArgs[1]!.isStrLit?.get!
  let out ← processExternal `testlanguage input
  return out


external testlanguage where
  "let" $n ":=" val "in" rest <==> let n := val; rest
  -- "test" <==> by grind

#eval do
  let expr ← processExternal `testlanguage "let x := 5 in x"
  logInfo m!"Elaborated expression: {expr}"

#eval process "let x := 5 in x"

-- external testlanguage where
--   "zero" <==> 0
--   "one" <==> 1
--   x "+" y <==> (x:Nat) + y
--   x "*" y <==> (x:Nat) * y
--   x "-" y <==> (x:Nat) - y
--   x "^" y <==> (x:Nat) ^ y
--   "(" x ")" <==> x
--   "let" $n ":=" bi "in" rest <==> let n := bi; rest
--   "fun" $n "->" rest <==> fun (n:Nat) => (rest:Nat)

-- #eval (process "let myfun := fun n -> (n + 0) ^ (1 + 1) in myfun") 1


#check MetavarContext
#check Term.saveState

/-TODO:
- Problems with MVar context; how to make sure that metavariable context can be reconstructed? Keep the MetavarContext around and use `restoreState`?
- Why no antiquot at the beginning of a line?
- How do deal with type annotations?
- Better handling of polymorphism for `let`, etc.
- Custom parser states
- Better error messages when metavariables can't be inferred fully
- Deal with metavar synthesis postponing if something doesn't work (for tactics etc)
- Wildcards/optional within patterns correspond to lists on the other side?
- Could we skip the entire elaboration step by just looking at the SyntaxNodeKind?
- Backtracking (in parsing too) for type filtration?
- Typechecking target expressions, maybe some theorems about correctness/roundtripability?
- Better logic for `num`s
- Blanks with the same name have enforced equality
- Stop using ExprPatterns! Just rely on Synthetic mvars as blanks; to fill, just set the correct value in MetavarContext and instantiate. This takes care of coupling and stuff.
-/
