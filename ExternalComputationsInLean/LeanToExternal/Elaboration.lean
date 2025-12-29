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
import Lean.Elab.Syntax


import ExternalComputationsInLean.Utils.Syntax
import ExternalComputationsInLean.Utils.Datatypes

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq



open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command




partial def Syntax.findAndReplaceM {m : Type → Type} [Monad m] (fn : Syntax → m (Option (Syntax × List Name))) : Syntax → m (Syntax × List Name)
  | stx@(Lean.Syntax.node info kind args) => do
    match (← fn stx) with
    | some stx => return stx
    | none     =>
        let (args, names) := (← args.mapM (Syntax.findAndReplaceM fn)).unzip
        return (Lean.Syntax.node info kind args, names.toList.flatten)
  | stx => do
    let o ← fn stx
    return o.getD (stx, [])
def TSyntax.findAndReplaceM {k : Name} {m : Type → Type} [Monad m] (fn : Syntax → m (Option (Syntax × List Name))) (stx : TSyntax k) : m (TSyntax k × List Name) :=
  do
    let (stx, names) ← Syntax.findAndReplaceM fn stx.1
    return (TSyntax.mk stx, names)




/-- Convert a `stx` node into a `macroArg` node for use in `expandMacroArg`. Identifiers, which are usually interpreted as parser categories, will instead be converted to the names of the bound variables, with the category being the supplied name (i.e. `x` => `x:mycategory`). -/
def toMacroArg (stx : TSyntax `stx) (cat : Name) : CommandElabM (TSyntax `Lean.Parser.Command.macroArg) := do
  -- Replace any identifiers (which are treated as parserCategories) with the category `cat`
  let (stx, names) ← TSyntax.findAndReplaceM (fun stx => do
    match stx with
    | Lean.Syntax.node _ `Lean.Parser.Syntax.cat children =>
      match children.toList with
      | (.ident _ name _ _) :: rest =>
        let new_children := (mkIdent cat).raw :: rest
        return some ((Lean.Syntax.node default `Lean.Parser.Syntax.cat new_children.toArray), [name.toName])
      | _ => return none
    | _ => return none) stx

  -- Should only be at most one identifier replaced (not sure how there could be multiple anyway)
  if names.length > 1 then throwError "assertion failed"

  -- Wrap to make it into a macroArg; add the identifier if there was one
  match names with
  | [] => return ⟨Lean.Syntax.node default `Lean.Parser.Command.macroArg #[(Lean.Syntax.node default `null #[]), stx.raw]⟩ -- No identifier, just an atom or something
  | _  => return ⟨Lean.Syntax.node default `Lean.Parser.Command.macroArg #[(Lean.Syntax.node default `null #[(mkIdent names[0]!), (Lean.Syntax.atom default ":")]), stx.raw]⟩


/-- Given a category name and an array of `stx` Syntax objects (treated as patterns), add a definition to the environment that matches that pattern (throwing an error otherwise) -/
def declareExternalElaborator (kind : SyntaxNodeKind) (cat : Name) (patterns : Array (TSyntax `stx)) (target : ExternalEquivalenceKey) : CommandElabM Unit := do
  let asMacroArgs ← patterns.mapM (fun a => toMacroArg a cat) -- Convert each of the syntax elements to MacroArgs
  let (_, patArgs) := (← asMacroArgs.mapM expandMacroArg).unzip -- Create antiquoted patterns that match them

  let equiv ← getExternalEquivalence target
  let vars ← match equiv with
  | none => throwError m!"No external equivalence found for '{target.name}'"
  | some e => pure e.variables
  let vars_stx : List Syntax ← vars.mapM (fun n => do
    let as_name : TSyntax `term := mkStrLit n.toString
    let as_ident : TSyntax `term := mkIdent n
    `(Prod.mk ($as_name).toName $as_ident))
  let vars_stx_array : TSepArray `term "," := TSepArray.mk vars_stx.toArray
  -- logInfo m!"{vars_stx_array.elemsAndSeps}"

  let pat : TSyntax `term := ⟨mkNode kind patArgs⟩
  let target : TSyntax `term := mkStrLit target.name.toString
  logInfo m!"{← `(([ $vars_stx_array,* ] : List (Name × Syntax)))}"
  let alts : TSyntaxArray ``matchAlt := #[← `(matchAltExpr| | `($pat) => pure ( ( ⟨($target).toName⟩ : ExternalEquivalenceKey), ([ $vars_stx_array,* ] : List (Name × Syntax)) ) )] -- The core of our match statement. We store the details about what we're elaborating to in an enivonment extension to avoid having to quote everything here.

  let mut k := kind
  if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
  if k == choiceKind then
    throwErrorAt alts[0]!
      "invalid alternative, multiple interpretations for pattern (solution: specify node kind using (kind := ...) ...`)"

  -- TODO: carry over attributes and maybe other stuff like doc comments? idk if this is necessary
  -- let attrs? : Option (TSepArray `Lean.Parser.Term.attrInstance ",") := none
  -- let attrKind := default
  -- let mkAttrs (kind : Name) : CommandElabM (TSyntaxArray ``attrInstance) := do
  --   let attr ← `(attrInstance| $attrKind:attrKind $(mkIdent kind):ident $(← mkIdentFromRef k):ident)
  --   pure <| match attrs? with
  --     | some attrs => attrs.getElems.push attr
  --     | none => #[attr]

  -- magic (from Lean.Elab.ElabRules)
  let alts ← alts.mapM fun (alt : TSyntax ``matchAlt) => match alt with
    | `(matchAltExpr| | $pats,* => $rhs) => do
      let pat := pats.elemsAndSeps[0]!
      if !pat.isQuot then
        throwUnsupportedSyntax
      let quoted := getQuotContent pat
      let k' := quoted.getKind
      if checkRuleKind k' k then
        pure alt
      else if k' == choiceKind then
          match quoted.getArgs.find? fun quotAlt => checkRuleKind quotAlt.getKind k with
          | none        => throwErrorAt alt "invalid elab_rules alternative, expected syntax node kind '{k}'"
          | some quoted =>
            let pat := pat.setArg 1 quoted
            let pats := ⟨pats.elemsAndSeps.set! 0 pat⟩
            `(matchAltExpr| | $pats,* => $rhs)
      else
        throwErrorAt alt "invalid elab_rules alternative, unexpected syntax node kind '{k'}'"
    | _ => throwUnsupportedSyntax

  -- Full matcher definition. We register it as a `external_elab` attribute so it can be conveniently found later (without having to mess around at the meta level)
  let attr ← `(attrInstance| $(mkIdent `external_elab):ident $(← mkIdentFromRef k):ident)
  let matcher_def : Syntax ← `(@[$attr]
      aux_def elabRules $(mkIdent k) : ExternalElabSignature :=
      fun stx _ => match stx with $alts:matchAlt* | _ => no_error_if_unused% throwUnsupportedSyntax)

  elabCommand matcher_def
