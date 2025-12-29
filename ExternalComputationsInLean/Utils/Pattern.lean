import Lean
import Qq.Macro
import ExternalComputationsInLean.Utils.Syntax

open Lean Elab Meta Term Expr
open Qq

/-- Represents a partially specified expression. `blank`s represent unspecified parts that must be filled using other patterns. These are kept distinct from `mvar`s to carry information about their name, to not have to worry about moving MVar contexts around, and to ensure we don't try to run "fill-in-the-blank" on stuff that should just be inferred by `instantiateMVars` instead of specified manually. -/
inductive ExprPattern
  | blank (id : MVarId) (type? : Option ExprPattern) (name : Name := Name.anonymous)
  | bvar (idx : Nat)
  | fvar (id : FVarId)
  | mvar (id : MVarId)
  | sort (l : Level)
  | const (declName : Name) (us : List Level)
  | app (f : ExprPattern) (arg : ExprPattern)
  | lam (binderName : Name) (binderType : ExprPattern) (body : ExprPattern) (bi : BinderInfo)
  | forallE (binderName : Name) (binderType : ExprPattern) (body : ExprPattern) (bi : BinderInfo)
  | letE (binderName : Name) (binderType : ExprPattern) (value : ExprPattern) (body : ExprPattern) (nondep: Bool)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : ExprPattern)
  deriving Inhabited, Repr

partial def ExprPattern.toMessageData (e : ExprPattern) : MessageData :=
  (match e with
  | .blank _ type? name =>
    match type? with
    | some t => m!"ExprPattern.blank {name} (type: {toMessageData t})"
    | none   => m!"ExprPattern.blank {name}"
  | .bvar idx => m!"ExprPattern.bvar {idx}"
  | .fvar id => m!"ExprPattern.fvar {id.name}"
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

partial def ExprPattern.toString (e : ExprPattern) : String :=
  (match e with
  | .blank _ type? name =>
    match type? with
    | some t => s!"ExprPattern.blank {name} (type: {toString t})"
    | none   => s!"ExprPattern.blank {name}"
  | .bvar idx => s!"ExprPattern.bvar {idx}"
  | .fvar id => s!"ExprPattern.fvar {id.name.toString}"
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


/-- Converts an `Expr` into an `ExprPattern`; assumes synthetically added metavariables represent blanks to fill in. Names of blanks are provided left to right through `varnames`. -/
partial def Lean.Expr.toPattern (e : Expr) (varnames : List Name) : MetaM ExprPattern := do
  return (← go e varnames).1
where
  go : Expr → List Name → MetaM (ExprPattern × List Name) := fun e varnames =>
  do
    match e with
    | .mvar _ => do
      match ← e.mvarId!.getKind with
      | MetavarKind.natural => return (.mvar (e.mvarId!), varnames)
      | _ =>
        let typ? : Option Expr ← try
          let x ← inferType e
          pure (some x)
        catch _ =>
          pure none

        match varnames with
        | name :: rest =>
          let (typ?, rest) ← match typ? with
          | some t =>
            let res ← go t rest
            pure (some res.1, res.2)
          | none => pure (none, rest)
          return (.blank (e.mvarId!) typ? name, rest)
        | _ => throwError "Not enough variable names provided to toPattern"
    | .const n ls => do return ⟨.const n ls, varnames⟩
    | .app f a => do
      let (f, varnames) ← go f varnames
      let (a, varnames) ← go a varnames
      return (.app f a, varnames)
    | .bvar i => do return ⟨.bvar i, varnames⟩
    | .fvar id => do return ⟨.fvar id, varnames⟩
    | .sort l => do return ⟨.sort l, varnames⟩
    | .forallE n t b bi => do
      let (t, varnames) ← go t varnames
      let (b, varnames) ← go b varnames
      return (.forallE n t b bi, varnames)
    | .lam n t b bi => do
      let (t, varnames) ← go t varnames
      let (b, varnames) ← go b varnames
      return (.lam n t b bi, varnames)
    | .letE n t v b bi => do
      let (t, varnames) ← go t varnames
      let (v, varnames) ← go v varnames
      let (b, varnames) ← go b varnames
      return (.letE n t v b bi, varnames)
    | .lit l => do return ⟨.lit l, varnames⟩
    | .proj s i e => do
      let (e, varnames) ← go e varnames
      return (.proj s i e, varnames)
    | .mdata _ e' => go e' varnames -- ignore metadata for now (IDK if there might be a future reason to keep it, but it'll just go out of scope anyway)

/-- Convert a `Syntax` object into an `ExprPattern`, with unknown identifiers assumed to correspond to blanks to be filled. TODO: bound variables and such, make sure names of blanks correspond to identifiers in the syntax pattern. -/
def Lean.Syntax.toPattern (stx : Syntax) (expectedType? : Option Expr) : TermElabM (ExprPattern × List Name) := do
  withoutModifyingElabMetaStateWithInfo do
    let (stx, varnames) ← collectAndReplaceUnknownIdents stx

    -- let e ← elabTerm stx expectedType?
    let ⟨e, _, _, _⟩ ← classifyMVars stx expectedType? -- I don't understand why, but this has slightly better behavior with regards to natural vs synthetic mvars than the normal `elabTerm`

    synthesizeSyntheticMVarsNoPostponing
    return (← (← instantiateMVars e).toPattern varnames, varnames)

/-- Convert a `Syntax` object into an `ExprPattern`, with unknown identifiers assumed to correspond to blanks to be filled. TODO: bound variables and such, make sure names of blanks correspond to identifiers in the syntax pattern. -/
def Lean.TSyntax.toPattern (stx : TSyntax `term) (expectedType? : Option Expr) : TermElabM (ExprPattern × List Name) :=
  stx.raw.toPattern expectedType?

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
  | .fvar id => q(ExprPattern.fvar $id)
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
    q(ExprPattern.lam $n $x $y $bi)
  | .forallE n t b bi =>
    let x : Q(ExprPattern) := t.quote
    let y : Q(ExprPattern) := b.quote
    q(ExprPattern.forallE $n $x $y $bi)
  | .letE n t v b bi =>
    let x : Q(ExprPattern) := t.quote
    let y : Q(ExprPattern) := v.quote
    let z : Q(ExprPattern) := b.quote
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
    if e.isFVar && e.fvarId! == id then
      return []
    else
      throwError "Pattern does not match"
  | _ => throwError "matchAndFormat: this pattern is not supported"

partial def ExprPattern.toExpr (pat : ExprPattern) : MetaM Expr := do
  match pat with
  | .bvar i => return mkBVar i
  | .fvar id => return mkFVar id
  | .mvar id => return mkMVar id
  | .sort l => return mkSort l
  | .const n ls => return mkConst n ls
  | .app f a => do
    let f' ← f.toExpr
    let a' ← a.toExpr
    return mkApp f' a'
  | .lam n t b bi => return mkLambda n bi (← t.toExpr) (← b.toExpr)
  | .forallE n t b bi => return mkForall n bi (← t.toExpr) (← b.toExpr)
  | .letE n t v b nondep => return mkLet n (← t.toExpr) (← v.toExpr) (← b.toExpr) nondep
  | .lit l => return mkLit l
  | .proj s i e => return mkProj s i (← e.toExpr)
  | _ => throwError "toExpr: this pattern is not supported"

-- attribute [ext] MVarId
-- instance : DecidableEq MVarId :=
--   fun a b => if h : a.name == b.name then .isTrue (by ext; simp_all) else .isFalse (by grind)

-- def ExprPattern.getBlanks (pat : ExprPattern) : Finset MVarId :=
--   match pat with
--   | .blank id => {id}
--   | .blankOfType id t => {id} ∪ t.getBlanks
--   | .app f a => f.getBlanks ∪ a.getBlanks
--   | .lam _ t b _ => t.getBlanks ∪ b.getBlanks
--   | .forallE _ t b _ => t.getBlanks ∪ b.getBlanks
--   | .letE _ t v b _ => t.getBlanks ∪ v.getBlanks ∪ b.getBlanks
--   | .proj _ _ e => e.getBlanks
--   | _ => ∅

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

partial def ExprPattern.unify (pat : ExprPattern) (blanks : List (Name × Expr)) : TermElabM Expr :=
  match pat with
  | .bvar i => return mkBVar i
  | .fvar id => return mkFVar id
  | .mvar id => return mkMVar id
  | .sort l => return mkSort l
  | .const n ls => return mkConst n ls
  | .app f a => do
    let f' ← f.unify blanks
    let a' ← a.unify blanks
    return mkApp f' a'
  | .lam n t b bi => return mkLambda n bi (← t.unify blanks) (← b.unify blanks)
  | .forallE n t b bi => return mkForall n bi (← t.unify blanks) (← b.unify blanks)
  | .letE n t v b nondep => return mkLet n (← t.unify blanks) (← v.unify blanks) (← b.unify blanks) nondep
  | .lit l => return mkLit l
  | .proj s i e => return mkProj s i (← e.unify blanks)
  | .blank _ _ name =>
    match blanks.find? (fun (n, _) => n == name) with
    | some (_, expr) => return expr
    | none => throwError m!"Unification failed: no value provided for blank '{name}'"
