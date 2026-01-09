import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import ExternalComputationsInLean.Utils.Pattern2
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term

import ExternalComputationsInLean.Utils.Syntax


open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal Parser Command Syntax Quote


/-- Creates a custom syntax declaration based on the patterns given; identifiers are assumed to refer to bound variable names not syntax categories. Lots borrowed from `elabSyntax` function in `Lean.Elab.Syntax` -/
def declareExternalSyntax (cat : Name) (patterns : Array Syntax) : CommandElabM (SyntaxNodeKind × List Name × List Name) := do
  let mut syntaxParts : Array Syntax := #[]
  let mut variableNames : List Name := []
  let mut binderNames : List Name := []
  for p in patterns do
    match p with
    | .node _ k args =>
      match k with
      | `Lean.Parser.Syntax.atom =>
        syntaxParts := syntaxParts.push p
      | `Lean.Parser.Syntax.cat =>
        match args.toList with
        | (.ident _ raw _ _ ) :: _ =>
          syntaxParts := syntaxParts.push (mkNode `Lean.Parser.Syntax.cat #[mkIdent cat])
          variableNames := (raw.toName) :: variableNames
        | _ => throwError m!"Unsupported cat args: {args}"
      | `stx.pseudo.antiquot =>
        match args.toList with
        | _ :: _ :: (.ident _ raw _ _ ) :: _ =>
          syntaxParts := syntaxParts.push (mkNode `Lean.Parser.Syntax.cat #[mkIdent `ident])
          binderNames := (raw.toName) :: binderNames
        | _ => throwError m!"Unsupported antiquot args: {args}"
      | _ => throwError m!"Unsupported syntax node kind: {k}"
    | x => throwError m!"Unsupported syntax part: {x}"


  let syntaxParser := mkNullNode syntaxParts
  let (val, lhsPrec?) ← runTermElabM fun _ => Term.toParserDescr syntaxParser cat

  -- Dummy variables for now
  let prio := 0
  let prec := 1024


  let name ← addMacroScopeIfLocal (← liftMacroM <| mkNameFromParserSyntax cat syntaxParser) default
  let idRef := mkIdentFrom (mkNullNode patterns) (cat.appendAfter "ParserDescr") (canonical := true)
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom idRef (cat.appendAfter "_parser") (canonical := true)
  let declName := mkIdentFrom idRef name (canonical := true)

  let attrInstance ← `(Term.attrInstance| $catParserId:ident $(quote prio):num)
  let attrInstances : TSepArray `Lean.Parser.Term.attrInstance "," := { elemsAndSeps := #[] }
  let attrInstances := attrInstances.push attrInstance


  let d ← if let some lhsPrec := lhsPrec? then
    `(@[$attrInstances,*] meta def $declName:ident : Lean.TrailingParserDescr :=
        ParserDescr.trailingNode $(quote stxNodeKind) $(quote prec) $(quote lhsPrec) $val)
  else
    `(@[$attrInstances,*] meta def $declName:ident : Lean.ParserDescr :=
        ParserDescr.node $(quote stxNodeKind) $(quote prec) $val)

  elabCommand d
  return (stxNodeKind, variableNames, binderNames)
