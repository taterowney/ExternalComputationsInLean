import Lean
import Qq.Macro
import ExternalComputationsInLean.Utils.Syntax

open Lean Elab Meta Term Expr
open Qq


structure ExprPattern where
  expr : AbstractMVarsResult
  vars : Array Name
  varMap : Std.HashMap MVarId Name
  binderVars : Array Name
deriving Inhabited


/-- Determines if a metavariable represents a blank to be filled by other patterns, or just inferred. TODO: distinction between blanks in different ExprPatterns -/
def ExprPattern.isBlank (self : ExprPattern) (mvars : Array Expr) (e : Expr) : TermElabM (Option Name) := do
  match e with
  | .mvar id =>
    let some idx := mvars.findIdx? (fun mv => mv.mvarId! == id) | throwError "Internal assertion failed in `isBlank`: mvar not found in pattern's mvar list"
    let some oldId := self.expr.mvars[idx]? | throwError "Internal assertion failed in `isBlank`: mvar id not found in abstracted mvar list"
    return self.varMap.get? oldId.mvarId!
  | _ => return none

/-- Elaborates to a hole that's type-independent of binders around it. -/
syntax (name := blankStx) "_blank" ident : term
@[term_elab blankStx]
def elabBlankStx : TermElab := fun stx expectedType? => do
  withLCtx {} {} do
    let t ← match expectedType? with
    | some typ => pure typ
    | none => mkFreshTypeMVar
    mkFreshExprSyntheticOpaqueMVar t (tag := stx.getArgs[1]!.getId)

def mkBlankId (userName : Name) := mkIdent (`_blankName ++ userName)

/-- A somewhat suspicious way of identifying unbound identifiers, replacing them with holes, and returning their names, while leaving binders and bound variables in place. Adapted from `Lean.Elab.Term.withAutoBoundImplicit`. -/
partial def repeatReplaceIdents (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × List Name) := do
  withReader (fun ctx => { ctx with autoBoundImplicit := true, autoBoundImplicits := {} }) do
    let rec loop (s : Lean.Elab.Term.SavedState) (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × List Name) := withIncRecDepth do
      checkSystem "auto-implicit"
      try
        -- let e ← elabTerm stx expectedType?
        let ⟨e, _, _, _⟩ ← classifyMVars stx expectedType? -- I don't understand why, but this has slightly better behavior with regards to natural vs synthetic mvars than the normal `elabTerm`
        return (e, [])
      catch
        | ex => match isAutoBoundImplicitLocalException? ex with
          | some n =>
            -- Restore state, declare `n`, and try again
            s.restore (restoreInfo := true)
            let out : TermElabM (Syntax × List Name) := Syntax.findAndReplaceM (fun stx => do
              match stx with
              | Lean.Syntax.ident _ val name _ =>
                if name == n then
                  let asIdent := mkBlankId val.toName
                  return some (← `( _blank $asIdent ), [val.toName])
                else
                  return none
              | _ => pure none
            ) stx
            let (stx', newNames) ← out

            let userName ←  match newNames with
              | name :: _ => pure name
              | _ => throwError m!"Internal error in `repeatReplaceIdents`: expected at least one name from findAndReplaceM"

            let ⟨e, names⟩ ← loop (← saveState) stx' expectedType?
            return (e, userName :: names)
          | none   =>
            throw ex
    loop (← saveState) stx expectedType?


private partial def getMVar : MVarId → TermElabM (List MVarId) := fun id => do
     return [id] ++ (← match (← id.getType) with
      | Expr.mvar id' => getMVar id'
      | _             => pure [])
def getAllMVarIds (e : Expr) : TermElabM (List MVarId) := do
  (← getMVars e).foldlM (fun acc id => do return acc ++ (← getMVar id)) []

def pairMVarNames (e : Expr) : TermElabM (Std.HashMap MVarId Name) := do
  let allMVars ← getAllMVarIds e
  let mvars ← allMVars.filterMapM (fun id => do
    match ← id.getKind with
      | .syntheticOpaque =>
        let tag ← id.getTag
        if (`_blankName).isPrefixOf tag then
          pure (some (id, tag.updatePrefix .anonymous))
        else pure none
      | _ => pure none
    )
  return Std.HashMap.ofList mvars


def checkVars (e : Expr) (varNames : Array Name) (pat_varNames : Array Name) (binderVarNames : Array Name) (checkInjective? : Bool := true) (checkSurjective? : Bool := true) : TermElabM Unit := do
  let rec collectBinderNames (e : Expr) : TermElabM (Array Name) :=
    match e with
    | .lam n t b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      return rest.push n
    | .forallE n t b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      return rest.push n
    | .letE n t v b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      let rest := rest ++ (← collectBinderNames v)
      return rest.push n
    | .app f a => do
      let fNames ← collectBinderNames f
      let aNames ← collectBinderNames a
      return fNames ++ aNames
    | .proj _ _ s => collectBinderNames s
    | .mdata _ b => collectBinderNames b
    | _ => return #[]

  let pat_binderVarNames ← collectBinderNames e

  if checkSurjective? then
    for n in pat_varNames do
      unless varNames.contains n do
        throwError m!"Variables don't match. Got {varNames} on lefthand side and {pat_varNames} on righthand side."
    -- Don't need to check surjectivity for binder names, since there can be binders that aren't variables (in which case they just keep their original names)

  if checkInjective? then
    for n in varNames do
      unless pat_varNames.contains n do
        throwError m!"Variables don't match. Got {varNames} on lefthand side and {pat_varNames} on righthand side."
    for n in binderVarNames do
      unless pat_binderVarNames.contains n do
        throwError m!"Binders don't match. Got {binderVarNames} on lefthand side and {pat_binderVarNames} on righthand side."


/-- Converts a `Syntax` into an `ExprPattern`. Names of variable binder names are provided left to right through `binderVars`. -/
def Lean.Syntax.toPattern (stx : Syntax) (expectedType? : Option Expr) (varNames : Array Name) (binderVarNames : Array Name) : TermElabM ExprPattern := do
  withoutModifyingElabMetaStateWithInfo do
    -- logInfo m!"Converting syntax to pattern: {stx.printdbg}"
    let (e, pat_varNames) ← repeatReplaceIdents stx expectedType?
    let paired ← pairMVarNames e
    -- logInfo m!"elaborated to {e}"

    unless pat_varNames.isPerm paired.values do
      throwError m!"Internal assertion failed in `toPattern`: variable names do not match replaced idents"

    checkVars e varNames pat_varNames.toArray binderVarNames

    synthesizeSyntheticMVarsNoPostponing
    return ExprPattern.mk (← abstractMVars e) pat_varNames.toArray paired binderVarNames

def Lean.TSyntax.toPattern {ks : Name} (stx : TSyntax ks) (expectedType? : Option Expr) (varNames : Array Name := #[]) (binderVarNames : Array Name := #[]) : TermElabM ExprPattern := do
  stx.raw.toPattern expectedType? varNames binderVarNames


def Lean.Expr.toPattern (e : Expr) (varNames : Array Name := #[]) (binderVarNames : Array Name := #[]) : TermElabM ExprPattern := do
  return ExprPattern.mk (← abstractMVars e) varNames (← pairMVarNames e) binderVarNames


/-- Turn an `ExprPattern` into an `Expr` by filling in the blanks with the provided expressions. -/
partial def ExprPattern.unify (self : ExprPattern) (blankContinuation : Name → TermElabM Expr) (identBlankContinuation : Name → TermElabM Name) : TermElabM Expr := do
  let (mvars, bis, e) ← openAbstractMVarsResult self.expr
  let out ← go e mvars
  instantiateMVars out
where
  go : Expr → Array Expr → TermElabM Expr := fun e mvars => do
    match e with
    | .mvar id =>
      match ← self.isBlank mvars e with
      | some name => do
        try
          let target ← blankContinuation name

          let _ ← go (← id.getType) mvars

          id.setKind .natural -- isDefEq can't assign `syntheticOpaque`s

          let updatedLCtx ← getLCtx
          setMCtx <| (← getMCtx).modifyExprMVarLCtx id (fun _ => updatedLCtx) -- TODO: This is probably unsafe in some situations; however, I can't figure out a nice way around it without refactoring everything. The mvar in question must be able to depend on the (newly created) fvars for `isDefEq` to work unfortunately. We could fix this by postponing the creation of the abstracted mvars until after the corresponding binder is created.

          unless ← isDefEq e target do
            throwError m!"Type mismatch when filling in blank '{name}': expected to unify with {e}, got {target}"
        catch e =>
          throwError m!"Type mismatch when filling in blank '{name}': {e.toMessageData}"
      | _ => pure ()
      return e
    | .app f a =>
      let f' ← go f mvars
      let a' ← go a mvars
      return .app f' a'
    | .proj n i s =>
      let s' ← go s mvars
      return .proj n i s'
    | .lam n t b bi =>
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      withLocalDecl binderName bi binderType fun binderExpr => do
        instantiateMVars <| ← mkLambdaFVars #[binderExpr] (← go b mvars) (binderInfoForMVars := bi)
    | .forallE n t b bi => do
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      withLocalDecl binderName bi binderType fun binderExpr => do
        mkForallFVars #[binderExpr] (← go b mvars) (binderInfoForMVars := bi)
    | .letE n t v b nondep => do
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      let valueExpr ← go v mvars

      -- let typ ← inferType valueExpr
      -- logInfo m!"Binder type: {binderType} ({t}), value type: {typ}"
      -- unless ← isDefEq typ binderType do -- For some reason the `isDefEq`s elsewhere sometimes miss this required equivalence
      --   throwError m!"Type mismatch in let-declaration for '{binderName}': expected {binderType}, got {typ}"

      withLetDecl binderName binderType valueExpr fun binderExpr => do
        let body ← go b mvars
        let out ← mkLetFVars #[binderExpr] body nondep
        return out
    | .fvar id =>
      let name ← try let x ← identBlankContinuation id.name; pure x catch _ => pure id.name
      match (← getLCtx).findFromUserName? name with
      | some ldecl => return mkFVar ldecl.fvarId
      | none => throwError m!"Unknown identifier '{name}'"
    | _ => return e





-- def ok : MetaM Expr := do
--   withLocalDecl `x default q(Nat) fun binderExpr => do
--     let m ← mkFreshExprMVar none

--     unless ← isDefEq m binderExpr do throwError m!"Couldn't unify :("
--     mkLambdaFVars #[binderExpr] m
-- #eval ok -- works fine

-- def bad : MetaM Expr := do
--   let m ← mkFreshExprMVar q(Nat)
--   withLocalDecl `x default q(Nat) fun binderExpr => do
--     -- let updatedLCtx ← getLCtx; setMCtx <| (← getMCtx).modifyExprMVarLCtx m.mvarId! (fun _ => updatedLCtx)


--     let out ← mkLambdaFVars #[binderExpr] m
--     logInfo m!"Out is {out.beta #[q(1)]}"

--     unless ← isDefEq (out.beta #[q(1)]) binderExpr do throwError m!"Couldn't unify 1 :("

--     unless ← isDefEq (out.beta #[q(1)]) m do throwError m!"Couldn't unify :("
--     pure out


-- #eval bad -- throws an error (want this to work)
