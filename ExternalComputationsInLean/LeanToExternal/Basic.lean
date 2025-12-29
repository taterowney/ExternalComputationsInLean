import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import ExternalComputationsInLean.Utils.Pattern
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term

import ExternalComputationsInLean.LeanToExternal.Parsing
import ExternalComputationsInLean.LeanToExternal.Elaboration

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal Parser Command Syntax Quote


declare_syntax_cat externalcat

/-- Set up parsing/elaboration rules for a specific external syntax pattern. -/
def declareExternal (cat : Name) (patterns : Array (TSyntax `stx)) (target : ExprPattern) (variables : List Name) : CommandElabM Unit := do
  let k ← declareExternalSyntax cat patterns
  addExternalEquivalence k cat k target variables
  declareExternalElaborator k cat (patterns.map (fun x => ⟨x⟩)) ⟨k⟩

/-- Parse an input string according to the external syntax category `cat`, returning the corresponding `Syntax` object. -/
def parseExternal (cat : Name) (input : String) : TermElabM Syntax := do
  let p := Parser.categoryParser cat 1 |>.fn -- Process the syntax with our custom parser
  let e ← getEnv
  let ctx := Parser.mkInputContext input "<input>"
  let out := p.run ctx {env := e, options := default} (Parser.getTokenTable e) {cache := Parser.initCacheForInput input, pos := 0}
  if out.hasError then
    throwError m!"Syntax error in input: {out.errorMsg}"
  return out.stxStack.back


/-- Elaborate a set of parsed external syntax, recursively filling in blanks. TODO: `elabContinuation` currently pretty simplistic: might want to add type filtration (requires delaboration?), interface with state/fvars, and maybe make it a parameter -/
partial def elabExternal (cat : Name) (input : Syntax) : TermElabM Expr := do
  match externalElabAttribute.getEntries (← getEnv) input.getKind with
  | [] => throwError m!"Internal assertion failed: no elaborator found for external syntax of kind '{input.getKind}'"
  | elab_fn :: _ =>
    logInfo m!"Using external elaborator '{elab_fn.declName}' for syntax of kind '{input.getKind}'"
    let (key, vals) ← elab_fn.value input none
    let some e ← liftCommandElabM <| getExternalEquivalence key | throwError m!"Internal assertion failed: no external equivalence found for key '{key.name}'"
    if e.variables.length != vals.length then
      throwError m!"Internal assertion failed: number of variables in external equivalence '{e.variables.length}' does not match number of provided values '{vals.length}'"
    elabContinuation cat e vals
where elabContinuation (cat : Name) (e : ExternalEquivalence) (vals : List (Name × Syntax)) : TermElabM Expr := do
  let pat := e.exprPattern
  let elaborated ← vals.mapM (fun (n, stx) => do
    let out ← elabExternal cat stx
    return (n, out))
  pat.unify elaborated

/-- Process (parse and elaborate) an input string according to the external syntax category `cat`. -/
def processExternal (cat : Name) (input : String) : TermElabM Expr := do
  let stx ← parseExternal cat input
  elabExternal cat stx
