import ExternalComputationsInLean.LeanToExternal.Basic
import Mathlib.Order.Interval.Set.Defs

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

  -- let opt : Options := Options.empty.setBool `linter.unused_variables false
  -- modify fun s => { s with maxRecDepth := maxRecDepth.get opt }
  -- modifyScope fun scope => { scope with opts := opt }

  initializeExternalCategory name

  let name := name.getId
  for line in lines do
    match line.raw.getArgs.toList with
    | [syntaxPat, _, targetExpr] =>
      let syntaxPats := syntaxPat.getArgs.map .mk
      let target : TSyntax `term := ⟨targetExpr⟩
      declareExternal name syntaxPats target
    | _ => throwError m!"Unsupported syntax: {line}"


syntax (name := processExternalCmd) "process" ident term : term
@[term_elab processExternalCmd]
def processExternalCmdImpl : TermElab := fun stx _ => do
  let cat : Name := stx.getArgs[1]!.getId
  let input : String := stx.getArgs[2]!.isStrLit?.get!
  let out ← processExternal cat input
  return out


-- external testlanguage where
--   "Nat" <==> Nat
--   "String" <==> String
--   -- x "==" y <==> x=y
--   -- "fun" $n "->" rest <==> fun n => rest
--   -- "fun" $n ":" ty "->" rest <==> fun (n : ty) => rest
--   -- "forall" $n ":" ty "," rest <==> ∀ (n : ty), rest
--   "let" $n ":" ty ":=" bi "in" rest <==> let n := (bi:ty); rest
--   -- "let" $n ":" ty ":=" bi "in" rest <==> let (n:ty) := bi; rest
--   x ":" y <==> (x : y)


-- #eval do
--   let expr ← processExternal `testlanguage "5:Nat"
--   logInfo m!"Elaborated expression: {expr}"

-- #eval do
--   let expr ← processExternal `testlanguage "fun test : String -> test"
--   logInfo m!"Elaborated expression: {expr}"

-- #eval do
--   let expr ← processExternal `testlanguage "forall test : String, test==test"
--   logInfo m!"Elaborated expression: {expr}"


-- #eval do
--   let expr ← processExternal `testlanguage "let test : String := 5 in test"
--   logInfo m!"Elaborated expression: {expr}"


-- #eval do
--   let expr ← processExternal `testlanguage "let test : String := 5 in test"
--   logInfo m!"Elaborated expression: {expr}"



-- external testlanguage2 where
--   "Nat" <==> Nat
--   "String" <==> String
--   x "+" y <==> (x:Nat) + y
--   x "*" y <==> (x:Nat) * y
--   x "-" y <==> (x:Nat) - y
--   x "^" y <==> (x:Nat) ^ y
--   "(" x ")" <==> x
--   x "==" y <==> x=y
--   "let" $n ":=" val "in" rest <==> let n := val; rest
--   "fun" $n "->" rest <==> fun n => rest
--   "forall" $n "," rest <==> ∀ n, rest
--   "let" $n ":" ty ":=" bi "in" rest <==> let n := (bi:ty); rest
--   -- "grind" <==> by grind
--   -- "[" x y "]" <==> Set.Icc x y




-- #eval do
--   let expr ← processExternal `testlanguage "let myfun := fun n -> (n + n) ^ 2 in myfun"
--   logInfo m!"Elaborated expression: {expr}"

-- #eval (process "let myfun := fun n -> (n + n) ^ 2 in myfun") 4




-- #check Lean.Meta.Simp.tryTheoremWithExtraArgs?

/-TODO:
- How do deal with type annotations?
- Type-ascribing `let` bindings (it puts another `lambda` in and screws up variable naming)
- Delay typeclass inference
- Custom parser states
- Deal with metavar synthesis postponing if something doesn't work (for tactics, function application, etc)
- Wildcards/optional within patterns correspond to lists on the other side?
- Could we skip the entire elaboration step by just looking at the SyntaxNodeKind?
- Backtracking (in parsing too) for type filtration?
- Typechecking target expressions, maybe some theorems about correctness/roundtripability?
- Better logic for `num`s
- Why no antiquot at the beginning of a line?
-/
