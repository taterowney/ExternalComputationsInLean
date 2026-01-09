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
import Lean.Elab.Syntax


import ExternalComputationsInLean.Utils.Syntax
import ExternalComputationsInLean.Utils.Datatypes

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq


partial def translateExpr (e : Expr) (patterns : Array ExprPattern) : MetaM String := do
  for pat in patterns do
    let (mvars, _, pat_expr) ← openAbstractMVarsResult pat.expr
    if (← isDefEqGuarded e pat_expr) then
      logInfo m!"matched pattern {pat_expr}"
      let blanks := (← getAllMVarsIds pat_expr).filterMapM (fun id => do
        if ← pat.isBlank id then
          some id
        else none)
