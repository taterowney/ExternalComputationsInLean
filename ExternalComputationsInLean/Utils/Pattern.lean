import Lean
import Qq.Macro
import ExternalComputationsInLean.Utils.Syntax

open Lean Elab Meta Term Expr
open Qq

inductive BinderName where
  | fixed (name : Name)
  | var (name : Name)
  deriving Inhabited, Repr, BEq


/-- Represents a partially specified expression. `blank`s represent unspecified parts that must be filled using other patterns. These are kept distinct from `mvar`s to carry information about their name, to not have to worry about moving MVar contexts around, and to ensure we don't try to run "fill-in-the-blank" on stuff that should just be inferred by `instantiateMVars` instead of specified manually. -/
inductive ExprPattern
  | blank (id : MVarId) (type? : Option ExprPattern) (name : Name := Name.anonymous)
  | bvar (idx : Nat)
  | fvar (id : BinderName)
  | mvar (id : MVarId)
  | sort (l : Level)
  | const (declName : Name) (us : List Level)
  | app (f : ExprPattern) (arg : ExprPattern)
  | lam (binderName : BinderName) (binderType : ExprPattern) (body : ExprPattern) (bi : BinderInfo)
  | forallE (binderName : BinderName) (binderType : ExprPattern) (body : ExprPattern) (bi : BinderInfo)
  | letE (binderName : BinderName) (binderType : ExprPattern) (value : ExprPattern) (body : ExprPattern) (nondep: Bool)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : ExprPattern)
  deriving Inhabited, Repr

instance : ToMessageData BinderName where
  toMessageData
    | .fixed name => m!"BinderName.fixed {name}"
    | .var name   => m!"BinderName.var {name}"

partial def ExprPattern.toMessageData (e : ExprPattern) : MessageData :=
  (match e with
  | .blank _ type? name =>
    match type? with
    | some t => m!"ExprPattern.blank {name} (type: {toMessageData t})"
    | none   => m!"ExprPattern.blank {name}"
  | .bvar idx => m!"ExprPattern.bvar {idx}"
  | .fvar id => m!"ExprPattern.fvar {id}"
  | .mvar id => m!"ExprPattern.mvar {id.name}"
  | .sort l => m!"ExprPattern.sort {l}"
  | .const declName us => m!"ExprPattern.const {declName} {us}"
  | .app f arg => m!"ExprPattern.app ({toMessageData f}) ({toMessageData arg})"
  | .lam binderName binderType body _ => m!"ExprPattern.lam {binderName} ({toMessageData binderType}) ({toMessageData body})"
  | .forallE binderName binderType body _ => m!"ExprPattern.forallE {binderName} ({toMessageData binderType}) ({toMessageData body})"
  | .letE binderName binderType value body _ => m!"ExprPattern.letE {binderName} ({toMessageData binderType}) ({toMessageData value}) ({toMessageData body})"
  | .lit l => m!"ExprPattern.lit {match l with
    | .natVal n => m!"(natVal {n})"
    | .strVal s => m!"(strVal {s})"}"
  | .proj structName idx e => m!"ExprPattern.proj {structName} {idx} ({toMessageData e})") ++ "\n"

instance : ToMessageData ExprPattern :=
  ⟨ExprPattern.toMessageData⟩

instance : ToString BinderName :=
  ⟨fun b =>
    match b with
    | .fixed name => s!"BinderName.fixed {name}"
    | .var name   => s!"BinderName.var {name}"⟩

partial def ExprPattern.toString (e : ExprPattern) : String :=
  (match e with
  | .blank _ type? name =>
    match type? with
    | some t => s!"ExprPattern.blank {name} (type: {toString t})"
    | none   => s!"ExprPattern.blank {name}"
  | .bvar idx => s!"ExprPattern.bvar {idx}"
  | .fvar id => s!"ExprPattern.fvar {id}"
  | .mvar id => s!"ExprPattern.mvar {id.name.toString}"
  | .sort l => s!"ExprPattern.sort {l}"
  | .const declName us => s!"ExprPattern.const {declName} {us}"
  | .app f arg => s!"ExprPattern.app ({toString f}) ({toString arg})"
  | .lam binderName binderType body _ => s!"ExprPattern.lam {binderName} ({toString binderType}) ({toString body})"
  | .forallE binderName binderType body _ => s!"ExprPattern.forallE {binderName} ({toString binderType}) ({toString body})"
  | .letE binderName binderType value body _ => s!"ExprPattern.letE {binderName} ({toString binderType}) ({toString value}) ({toString body})"
  | .lit l => match l with
    | .natVal n => s!"ExprPattern.lit (natVal {n})"
    | .strVal s => s!"ExprPattern.lit (strVal {s})"
  | .proj structName idx e => s!"ExprPattern.proj {structName} {idx} ({toString e})") ++ "\n"

instance : ToString ExprPattern :=
  ⟨ExprPattern.toString⟩


instance : BEq MetavarKind where
  beq
    | MetavarKind.natural, MetavarKind.natural => true
    | MetavarKind.synthetic, MetavarKind.synthetic => true
    | MetavarKind.syntheticOpaque, MetavarKind.syntheticOpaque => true
    | _, _ => false

/-- Convert the name of an identifier into a `BinderName`, which may represent a fixed name or a name that depends on what is parsed externally. -/
def Lean.Name.toBinderName (n : Name) (variableBinders : List Name): BinderName :=
  match variableBinders.find? (fun bn => bn == n) with
  | some _ => BinderName.var n
  | none   => BinderName.fixed n


/-- Converts an `Expr` into an `ExprPattern`. Names of blanks are provided left to right through `varnames`. -/
partial def Lean.Expr.toPattern (e : Expr) (variableBinders : List Name) : MetaM ExprPattern := do
  go e
where
  go (e : Expr) : MetaM ExprPattern := do
    match e with
    | .mvar _ => do
      match ← e.mvarId!.getKind with
      | MetavarKind.syntheticOpaque =>
        let tag ← e.mvarId!.getTag
        if (`_blankName).isPrefixOf tag then
          let tag := tag.updatePrefix .anonymous -- Extract the user-facing name of the blank
          logInfo m!"Triggered blank: {e} with tag {tag}"
          let typ? : Option Expr ← try
            let x ← inferType e
            pure (some x)
          catch _ =>
            pure none

          let typ? ← match typ? with
          | some t =>
            let res ← go t
            pure (some res)
          | none => pure none
          return .blank (e.mvarId!) typ? tag

        else
          return .mvar (e.mvarId!)
      | _ => return .mvar (e.mvarId!)
    | .const n ls => do return .const n ls
    | .app f a => do
      let f ← go f
      let a ← go a
      return .app f a
    | .bvar i => do return .bvar i
    | .fvar id => do return .fvar (id.name.toBinderName variableBinders)
    | .sort l => do return .sort l
    | .forallE n t b bi => do
      let t ← go t
      let b ← go b
      return .forallE (n.toBinderName variableBinders) t b bi
    | .lam n t b bi => do
      let t ← go t
      let b ← go b
      return .lam (n.toBinderName variableBinders) t b bi
    | .letE n t v b bi => do
      let t ← go t
      let v ← go v
      let b ← go b
      return .letE (n.toBinderName variableBinders) t v b bi
    | .lit l => do return .lit l
    | .proj s i e => do
      let e ← go e
      return .proj s i e
    | .mdata _ e' => go e' -- ignore metadata for now (IDK if there might be a future reason to keep it, but it'll just go out of scope anyway)


/-- Elaborates to a hole that's type-independent of binders around it. -/
syntax (name := blankStx) "_blank" ident : term
@[term_elab blankStx]
def elabBlankStx : TermElab := fun stx expectedType? => do
  withLCtx {} {} do
    match expectedType? with
    | some t => mkFreshExprSyntheticOpaqueMVar t (tag := `_blankName ++ stx.getArgs[1]!.getId)
    | none => postponeElabTerm stx expectedType?


/-- A somewhat suspicious way of identifying unbound identifiers, replacing them with holes, and returning their names, while leaving binders and bound variables in place. Adapted from `Lean.Elab.Term.withAutoBoundImplicit`. -/
partial def repeatReplaceIdents (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × List Name) := do
  withReader (fun ctx => { ctx with autoBoundImplicit := true, autoBoundImplicits := {} }) do
    let rec loop (s : Lean.Elab.Term.SavedState) (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × List Name) := withIncRecDepth do
      checkSystem "auto-implicit"
      try
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
                  -- logInfo m!"Replacing identifier {val} ({name}) with blank"
                  let asIdent := mkIdent val.toName
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
          | none   => throw ex
    loop (← saveState) stx expectedType?


/-- Convert a `Syntax` object into an `ExprPattern`, with unknown identifiers assumed to correspond to blanks to be filled. Also returns the context of the metavariables used in the pattern. `varnames` represents a list of the names of variables to be determined upon elaboration, while `variableBinders` is a list of the names of binders that are shared between Lean and the DSL. TODO: bound variables and such, make sure variable binders line up. -/
def Lean.Syntax.toPattern (stx : Syntax) (expectedType? : Option Expr) (varnames : List Name) (variableBinders : List Name) : TermElabM (ExprPattern × MetavarContext) := do
  withoutModifyingElabMetaStateWithInfo do

    let (e, pat_varnames) ← repeatReplaceIdents stx expectedType?
    logInfo m!"Extracted {e}"

    unless varnames.isPerm pat_varnames do
      throwError m!"Variable names do not match. Expected: {varnames}, got: {pat_varnames}"

    synthesizeSyntheticMVarsNoPostponing

    logInfo m!"Full : {← (← instantiateMVars e).toPattern variableBinders}"
    -- let x ← getMCtx
    return (← (← instantiateMVars e).toPattern variableBinders, ← getMCtx)

/-- Convert a `Syntax` object into an `ExprPattern`, with unknown identifiers assumed to correspond to blanks to be filled. TODO: bound variables and such, make sure names of blanks correspond to identifiers in the syntax pattern. -/
def Lean.TSyntax.toPattern (stx : TSyntax `term) (expectedType? : Option Expr) (varnames : List Name) (variableBinders : List Name) : TermElabM (ExprPattern × MetavarContext) :=
  stx.raw.toPattern expectedType? varnames variableBinders


def BinderName.quote (b : BinderName) : Q(BinderName) :=
  match b with
  | .fixed name => q(BinderName.fixed $name)
  | .var name   => q(BinderName.var $name)

def ExprPattern.quote (e : ExprPattern) : Q(ExprPattern) :=
  match e with
  | .blank id type? name =>
    match type? with
    | some t =>
      let x : Q(ExprPattern) := t.quote
      q(ExprPattern.blank $id (some $x) $name)
    | none =>
      q(ExprPattern.blank $id none $name)
  | .bvar i => q(ExprPattern.bvar $i)
  | .fvar id =>
    let id : Q(BinderName) := id.quote
    q(ExprPattern.fvar $id)
  | .mvar id => q(ExprPattern.mvar $id)
  | .sort l => q(ExprPattern.sort $l)
  | .const n ls => q(ExprPattern.const $n $ls)
  | .app f a =>
    let x : Q(ExprPattern) := f.quote
    let y : Q(ExprPattern) := a.quote
    q(ExprPattern.app $x $y)
  | .lam n t b bi =>
    let x : Q(ExprPattern) := t.quote
    let y : Q(ExprPattern) := b.quote
    let n : Q(BinderName) := n.quote
    q(ExprPattern.lam $n $x $y $bi)
  | .forallE n t b bi =>
    let x : Q(ExprPattern) := t.quote
    let y : Q(ExprPattern) := b.quote
    let n : Q(BinderName) := n.quote
    q(ExprPattern.forallE $n $x $y $bi)
  | .letE n t v b bi =>
    let x : Q(ExprPattern) := t.quote
    let y : Q(ExprPattern) := v.quote
    let z : Q(ExprPattern) := b.quote
    let n : Q(BinderName) := n.quote
    q(ExprPattern.letE $n $x $y $z $bi)
  | .lit l => q(ExprPattern.lit $l)
  | .proj s i e =>
    let x : Q(ExprPattern) := e.quote
    q(ExprPattern.proj $s $i $x)

/- Evaluates if two patterns will always match the same expressions -/
partial def ExprPattern.isEquivalent (e1 e2 : ExprPattern) : Bool :=
  match (e1, e2) with
  | (.blank _ _ _, .blank _ _ _) => true
  | (.bvar i1, .bvar i2) => i1 == i2 -- TODO: check the logic around BVars (will indices be different even in equivalent patterns?)
  | (.fvar id1, .fvar id2) => id1 == id2
  | (.mvar _, .mvar _) => true -- Ideally matching the rest of the expression will ensure that enough constraints are placed on the metavariables for them to be equivalent
  | (.sort l1, .sort l2) => l1 == l2
  | (.const n1 ls1, .const n2 ls2) => n1 == n2 && ls1 == ls2
  | (.app f1 a1, .app f2 a2) => f1.isEquivalent f2 && a1.isEquivalent a2
  | (.lam n1 t1 b1 bi1, .lam n2 t2 b2 bi2) => n1 == n2 && t1.isEquivalent t2 && b1.isEquivalent b2 && bi1 == bi2
  | (.forallE n1 t1 b1 bi1, .forallE n2 t2 b2 bi2) => n1 == n2 && t1.isEquivalent t2 && b1.isEquivalent b2 && bi1 == bi2
  | (.letE n1 t1 v1 b1 bi1, .letE n2 t2 v2 b2 bi2) => n1 == n2 && t1.isEquivalent t2 && v1.isEquivalent v2 && b1.isEquivalent b2 && bi1 == bi2
  | (.lit l1, .lit l2) => l1 == l2
  | (.proj s1 i1 e1, .proj s2 i2 e2) => s1 == s2 && i1 == i2 && e1.isEquivalent e2
  | _ => false

/- Applies a function to every blank in the pattern, replacing it with the result. TODO: apply to types of blanks? -/
def ExprPattern.forEachBlank (e : ExprPattern) (fn : ExprPattern → ExprPattern) : ExprPattern :=
  match e with
  | .blank _ _ _ => fn e
  | .app f a => .app (f.forEachBlank fn) (a.forEachBlank fn)
  | .lam n t b bi => .lam n (t.forEachBlank fn) (b.forEachBlank fn) bi
  | .forallE n t b bi => .forallE n (t.forEachBlank fn) (b.forEachBlank fn) bi
  | .letE n t v b bi => .letE n (t.forEachBlank fn) (v.forEachBlank fn) (b.forEachBlank fn) bi
  | .proj s i e => .proj s i (e.forEachBlank fn)
  | _ => e

/- Monadic version of forEachBlank -/
def ExprPattern.forEachBlankM [Monad m] (e : ExprPattern) (fn : ExprPattern → m ExprPattern) : m ExprPattern := do
  match e with
  | .blank _ _ _ => fn e
  | .app f a =>
    let f' ← f.forEachBlankM fn
    let a' ← a.forEachBlankM fn
    return .app f' a'
  | .lam n t b bi =>
    let t' ← t.forEachBlankM fn
    let b' ← b.forEachBlankM fn
    return .lam n t' b' bi
  | .forallE n t b bi =>
    let t' ← t.forEachBlankM fn
    let b' ← b.forEachBlankM fn
    return .forallE n t' b' bi
  | .letE n t v b bi =>
    let t' ← t.forEachBlankM fn
    let v' ← v.forEachBlankM fn
    let b' ← b.forEachBlankM fn
    return .letE n t' v' b' bi
  | .proj s i e =>
    let e' ← e.forEachBlankM fn
    return .proj s i e'
  | _ => return e


/- Attempts to match an expression against a pattern, returning the results of elaborating each blank in the pattern -/
partial def ExprPattern.match {α : Type} (pat : ExprPattern) (e : Expr) (elabContinuation : Expr → MetaM α := (fun _ => throwError "Not implemented")) : MetaM (List α) := do
  match pat with
  | .blank _ typ? _ =>
    match typ? with
    | some t =>
      let t' ← inferType e
      let _ ← t.match t' elabContinuation
    | none => pure ()
    return [← elabContinuation e]
  | .const c _ =>
    if e.isConstOf c then
      return []
    else
      throwError "Pattern does not match"
  | .sort l =>
    if e.isSort then
      if l.isMVar then -- Hacky solution for now; should make this a real pattern
        return []
      else if l == e.sortLevel! then
        return []
      else
        throwError "Pattern does not match"
    else
      throwError "Pattern does not match"
  | .app f arg =>
    if h : e.isApp then
      return (← f.match (e.appFn h) elabContinuation) ++ (← arg.match e.appArg! elabContinuation)
    else
      throwError "Pattern does not match"
  | .lit l =>
    if e.isLit && l == e.litValue! then
      return []
    else
      throwError "Pattern does not match"
  | .forallE _ binder body _ =>
    if e.isForall then
      let res1 ← binder.match e.bindingDomain! elabContinuation
      let res2 ← body.match e.getForallBody elabContinuation
      return res1 ++ res2
    else
      throwError "Pattern does not match"
  | .mvar _ =>
    return []
  | .fvar id =>
    match id with
      | .fixed name =>
      if e.isFVar && e.fvarId! == ⟨name⟩ then
        return []
      else
        throwError "Pattern does not match"
      | _ => throwError "match: this pattern is not supported"
  | _ => throwError "matchAndFormat: this pattern is not supported"

def BinderName.toName (b : BinderName) : MetaM Name := do
  match b with
  | .fixed name => return name
  | .var name   => throwError m!"This pattern contains identifier variables that haven't been resolved: {name}"

partial def ExprPattern.toExpr (pat : ExprPattern) : MetaM Expr := do
  match pat with
  | .bvar i => return mkBVar i
  | .fvar id => return mkFVar ⟨← id.toName⟩
  | .mvar id => return mkMVar id
  | .sort l => return mkSort l
  | .const n ls => return mkConst n ls
  | .app f a => do
    let f' ← f.toExpr
    let a' ← a.toExpr
    return mkApp f' a'
  | .lam n t b bi => return mkLambda (← n.toName) bi (← t.toExpr) (← b.toExpr)
  | .forallE n t b bi => return mkForall (← n.toName) bi (← t.toExpr) (← b.toExpr)
  | .letE n t v b nondep => return mkLet (← n.toName) (← t.toExpr) (← v.toExpr) (← b.toExpr) nondep
  | .lit l => return mkLit l
  | .proj s i e => return mkProj s i (← e.toExpr)
  | _ => throwError "toExpr: this pattern contains blanks that haven't been fully resolved."


def ExprPattern.getBlanks (pat : ExprPattern) : List Name :=
  match pat with
  | .blank _ _ name => [name]
  | .app f a => f.getBlanks ++ a.getBlanks
  | .lam _ t b _ => t.getBlanks ++ b.getBlanks
  | .forallE _ t b _ => t.getBlanks ++ b.getBlanks
  | .letE _ t v b _ => t.getBlanks ++ v.getBlanks ++ b.getBlanks
  | .proj _ _ e => e.getBlanks
  | _ => []

def ExprPattern.fillBlank (pat : ExprPattern) (id : MVarId) (replacement : ExprPattern) : ExprPattern :=
  pat.forEachBlank fun e =>
    match e with
    | .blank bid _ _ => if bid == id then replacement else e
    | _ => e

def ExprPattern.isBlank (pat : ExprPattern) : Bool :=
  match pat with
  | .blank _ _ _ => true
  | _ => false

instance : BEq ExprPattern where
  beq e1 e2 :=
    e1.isEquivalent e2


-- def BinderName.unify (b : BinderName) (identBlanks : List (Name × Name)) : TermElabM Name := do
--   match b with
--   | .fixed name => return name
--   | .var name =>
--     match identBlanks.find? (fun (n, _) => n == name) with
--     | some (_, resolvedName) => return resolvedName
--     | none => throwError m!"Unification failed: no value provided for identifier blank '{name}'"


-- /-- Turn an `ExprPattern` into an `Expr` by filling in the blanks with the provided expressions. -/
-- partial def ExprPattern.unify (pat : ExprPattern) (blanks : List (Name × Expr)) (identBlanks : List (Name × Name)) : TermElabM Expr :=
--   match pat with
--   | .bvar i => return mkBVar i
--   | .fvar id => do
--     let lctx ← getLCtx
--     let unified ← id.unify identBlanks
--     match lctx.findFromUserName? unified with
--     | some ldecl => return mkFVar ldecl.fvarId
--     | none => throwError m!"Unification failed: no local declaration found for fvar '{unified}'"
--   | .mvar id => do
--     logInfo m!"Creating mvar for {id}"
--     -- mkFreshExprMVarWithId id
--     mkFreshExprMVar none
--   | .sort l => return mkSort l
--   | .const n ls => return mkConst n ls
--   | .app f a => do
--     let f' ← f.unify blanks identBlanks
--     let a' ← a.unify blanks identBlanks
--     return mkApp f' a'
--   | .lam n t b bi => do
--     let binderName ← n.unify identBlanks
--     let binderType ← t.unify blanks identBlanks
--     let binderExpr ← mkFreshExprSyntheticOpaqueMVar binderType binderName
--     mkLambdaFVars #[binderExpr] (← b.unify blanks identBlanks) (binderInfoForMVars := bi)
--     -- return mkLambda (← n.unify identBlanks) bi (← t.unify blanks identBlanks) (← b.unify blanks identBlanks)
--   | .forallE n t b bi => do
--     let binderName ← n.unify identBlanks
--     let binderType ← t.unify blanks identBlanks
--     let binderExpr ← mkFreshExprSyntheticOpaqueMVar binderType binderName
--     mkForallFVars #[binderExpr] (← b.unify blanks identBlanks) (binderInfoForMVars := bi)
--     -- return mkForall (← n.unify identBlanks) bi (← t.unify blanks identBlanks) (← b.unify blanks identBlanks)
--   | .letE n t v b nondep => do
--     let binderName ← n.unify identBlanks
--     let binderType ← t.unify blanks identBlanks
--     let valueExpr ← v.unify blanks identBlanks
--     withLetDecl binderName binderType valueExpr fun binderExpr => do
--       mkLetFVars #[binderExpr] (← b.unify blanks identBlanks) nondep
--     -- return mkLet (← n.unify identBlanks) (← t.unify blanks identBlanks) (← v.unify blanks identBlanks) (← b.unify blanks identBlanks) nondep
--   | .lit l => return mkLit l
--   | .proj s i e => return mkProj s i (← e.unify blanks identBlanks)
--   | .blank _ _ name =>
--     match blanks.find? (fun (n, _) => n == name) with
--     | some (_, expr) => return expr
--     | none => throwError m!"Unification failed: no value provided for blank '{name}'"


def BinderName.unify' (b : BinderName) (identBlankContinuation : Name → TermElabM Name) : TermElabM Name := do
  match b with
  | .fixed name => return name
  | .var name   =>
    identBlankContinuation name

/-- Turn an `ExprPattern` into an `Expr` by filling in the blanks with the provided expressions. -/
partial def ExprPattern.unify' (pat : ExprPattern) (blankContinuation : Name → TermElabM Expr) (identBlankContinuation : Name → TermElabM Name) : TermElabM Expr :=
  match pat with
  | .bvar i => return mkBVar i
  | .fvar id => do
    let lctx ← getLCtx
    let unified ← id.unify' identBlankContinuation
    match lctx.findFromUserName? unified with
    | some ldecl => return mkFVar ldecl.fvarId
    | none => throwError m!"Unification failed: no local declaration found for fvar '{unified}'"
  | .mvar id => do
    logInfo m!"Creating mvar for {id.name}"
    mkFreshExprMVarWithId id
  | .sort l => return mkSort l
  | .const n ls => return mkConst n ls
  | .app f a => do
    let f' ← f.unify' blankContinuation identBlankContinuation
    let a' ← a.unify' blankContinuation identBlankContinuation
    return mkApp f' a'
  | .lam n t b bi => do
    let binderName ← n.unify' identBlankContinuation
    let binderType ← t.unify' blankContinuation identBlankContinuation
    withLocalDecl binderName bi binderType fun binderExpr => do
      mkLambdaFVars #[binderExpr] (← b.unify' blankContinuation identBlankContinuation) (binderInfoForMVars := bi)
  | .forallE n t b bi => do
    let binderName ← n.unify' identBlankContinuation
    let binderType ← t.unify' blankContinuation identBlankContinuation
    withLocalDecl binderName bi binderType fun binderExpr => do
      mkForallFVars #[binderExpr] (← b.unify' blankContinuation identBlankContinuation) (binderInfoForMVars := bi)
  | .letE n t v b nondep => do
    let binderName ← n.unify' identBlankContinuation
    let binderType ← t.unify' blankContinuation identBlankContinuation
    let valueExpr ← v.unify' blankContinuation identBlankContinuation
    withLetDecl binderName binderType valueExpr fun binderExpr => do
      let body ← b.unify' blankContinuation identBlankContinuation
      let out ← mkLetFVars #[binderExpr] body nondep
      try
        unless ← isDefEq (← inferType out) (← inferType body) do
          throwError m!"Type mismatch in let binding: {← inferType out} vs {← inferType body}"
      catch _ =>
        pure ()
      try
        unless ← isDefEq (← inferType binderExpr) (← inferType valueExpr) do
          throwError m!"Type mismatch in let binding: {← inferType out} vs {← inferType body}"
      catch _ =>
        pure ()
      return out
  | .lit l => return mkLit l
  | .proj s i e => return mkProj s i (← e.unify' blankContinuation identBlankContinuation)
  | .blank _ _ name =>
    blankContinuation name
