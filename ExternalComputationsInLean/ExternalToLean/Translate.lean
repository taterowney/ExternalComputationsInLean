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
import ExternalComputationsInLean.LeanToExternal.Basic

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq



partial def findTargetBinderName (pattern : Expr) (target : Expr) (binderName : Name) : TermElabM Name := do
  match (pattern, target) with
  | (Expr.forallE n ty body _, Expr.forallE n' ty' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName body body' binderName
  | (Expr.lam n ty body _, Expr.lam n' ty' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName body body' binderName
  | (Expr.letE n ty val body _, Expr.letE n' ty' val' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName val val' binderName <|>
      findTargetBinderName body body' binderName
  | _ => throwError "Binder name not found in pattern"


partial def Lean.Expr.printdbg (e : Expr) : String :=
  match e with
  | Expr.bvar idx => s!"bvar({idx})"
  | Expr.fvar id => s!"fvar({id.name})"
  | Expr.mvar id => s!"mvar({id.name})"
  | Expr.sort l => s!"sort({l})"
  | Expr.const id ls => s!"const({id}, {ls})"
  | Expr.app f a => s!"app({f.printdbg}, {a.printdbg})"
  | Expr.lam n ty body _ => s!"lam({n}, {ty.printdbg}, {body.printdbg})"
  | Expr.forallE n ty body _ => s!"forallE({n}, {ty.printdbg}, {body.printdbg})"
  | Expr.letE n ty val body _ => s!"letE({n}, {ty.printdbg}, {val.printdbg}, {body.printdbg})"
  | Expr.lit l => s!"lit()"
  | Expr.proj n idx struct => s!"proj({n}, {idx}, {struct})"
  | Expr.mdata md e => s!"mdata({md}, {e.printdbg})"





partial def makeMVarsDependent (e : Expr) (mvarIds : List MVarId) : TermElabM Expr := do
  let ⟨e', _⟩ ← go e mvarIds []
  -- logInfo m!"Original: {e} ({e.printdbg})"
  -- logInfo m!"New: {e'} ({e'.printdbg})"
  unless ← isDefEqGuarded e e' do
    throwError "Internal assertion failed: makeMVarsDependent couldn't reconstruct expression properly"
  return e
where go : Expr → List MVarId → List Expr → TermElabM (Expr × List MVarId) := fun e mvarIds binderTypes =>
do
  match e with
  | .mvar id =>
    if mvarIds.contains id then
      let rec mkMVarType (binderTypes : List Expr) : TermElabM Expr := do
        match binderTypes with
        | ty :: rest =>
          let inner ← mkMVarType rest
          mkArrow ty inner
        | _ => inferType e
      -- logInfo m!"Type of new mvar: {(← mkMVarType binderTypes)}"
      let rec addBVars (mvar : Expr) (depth : Nat) : Expr :=
        match depth with
        | 0 => mvar
        | _ => addBVars (Expr.app mvar (Expr.bvar (depth - 1))) (depth - 1)

      return (addBVars (← mkFreshExprMVar (some (← mkMVarType binderTypes))) binderTypes.length, mvarIds.filter (fun mid => mid != id))
    else
      return (e, mvarIds)
  | .lam n ty body info =>
    let (ty', mvarIds') ← go ty mvarIds binderTypes
    let (body', mvarIds'') ← go body mvarIds' (ty' :: binderTypes)
    return (.lam n ty' body' info, mvarIds'')
  | .forallE n ty body info =>
    let (ty', mvarIds') ← go ty mvarIds binderTypes
    let (body', mvarIds'') ← go body mvarIds' (ty' :: binderTypes)
    return (.forallE n ty' body' info, mvarIds'')
  | .letE n ty val body info =>
    let (ty', mvarIds') ← go ty mvarIds binderTypes
    let (val', mvarIds'') ← go val mvarIds' binderTypes
    let (body', mvarIds''') ← go body mvarIds'' (ty' :: binderTypes)
    return (.letE n ty' val' body' info, mvarIds''')
  | .app f a =>
    let (f', mvarIds') ← go f mvarIds binderTypes
    let (a', mvarIds'') ← go a mvarIds' binderTypes
    return (.app f' a', mvarIds'')
  | .mdata md e' =>
    let (e'', mvarIds') ← go e' mvarIds binderTypes
    return (.mdata md e'', mvarIds')
  | .proj n idx struct =>
    let (struct', mvarIds') ← go struct mvarIds binderTypes
    return (.proj n idx struct', mvarIds')
  | _ => return (e, mvarIds)


partial def translateExpr (cat : Name) (patterns : Array ExternalEquivalence) (e : Expr) (depth := 0) : TermElabM String := do
  if depth > 10000 then
    throwError m!"Exceeded maximum recursion depth when translating expression {e}. There's probably an infinite loop in the DSL somewhere."

  for pat in patterns do
    match pat.exprPattern with
    | .postponed _ => continue
    | .eager p =>
      let (_, _, pat_expr, blankMap) ← p.unpackExpr

      if pat.stxNodeKind == (externalNumKind (mkIdent cat)) then -- TODO: nat? seems to malfunction randomly
        if e.nat?.isSome || e.isRawNatLit then
          return (← PrettyPrinter.ppExpr e).pretty -- Special case: external number literals
        else
          continue

      else
      -- logInfo m!"Trying pattern {pat_expr.printdbg} for expression {e.printdbg}"
      if (← isDefEqGuarded pat_expr e) then
        let filledBlanks ← blankMap.keys.mapM (fun id => do translateExpr cat patterns (← instantiateMVars (Expr.mvar id)) (depth + 1))
        let filledMap := Std.HashMap.ofList (blankMap.values.zip filledBlanks)

        let mut result := ""
        for chunk in pat.rawSyntaxPatterns do

          match chunk with
          | .node _ k args =>
            match k with
            | `Lean.Parser.Syntax.atom =>
              match args.toList with
              | .node _ _ atomArgs :: _ =>
                match atomArgs.toList with
                | (.atom _ raw ) :: _ => -- If this part of the pattern is just a literal, put it in the output directly
                  result := result ++ " " ++ (raw.take (raw.length - 1) |>.takeRight (raw.length - 2)) -- Strip away the quotes
                | _ => throwError m!"Unable to turn atom pattern into string: {atomArgs.map (fun x => x.printdbg)}"
              | _ => throwError m!"Unable to turn atom pattern into string: {args.map (fun x => x.printdbg)}"
            | `Lean.Parser.Syntax.cat =>
              match args.toList with
              | (.ident _ raw _ _ ) :: _ => -- If this part of the pattern is a blank, look up what we filled it with
                match filledMap.get? raw.toName with
                | some str => result := result ++ " " ++ str
                | none => throwError m!"Internal error: no filled string for blank {raw.toName}"
              | _ => throwError m!"Unable to turn pattern into string: {args}"
            | `stx.pseudo.antiquot =>
              match args.toList with
              | _ :: _ :: (.ident _ raw _ _ ) :: _ => -- If this part of the pattern is an identifier variable, find the corresponding identifier's name
                -- logInfo m!"{pat_expr} {e} {raw.toName}"
                let binderName ← findTargetBinderName pat_expr e raw.toName
                result := result ++ " " ++ (if binderName.isAnonymous then "x" else binderName.toString)
              | _ => throwError m!"Unsupported antiquot args: {args}"
            | _ => throwError m!"Unsupported syntax node kind: {k}"
          | x => throwError m!"Unsupported syntax part: {x.printdbg}"
        return result.trim

  throwError m!"No matching pattern found for expression {e}"

def toExternal (cat : Name) (e : Expr) : TermElabM String := do
  let patterns ← liftCommandElabM <| getExternalEquivalencesForCategory cat
  let p1 :: _ := patterns.toList | throwError m!"No external equivalences found for category '{cat}'"
  unless p1.isInjective do
    throwError m!"Translation to external syntax failed: external equivalence for category '{cat}' is not injective, cannot translate from Lean expression to external syntax"

  translateExpr cat patterns e
