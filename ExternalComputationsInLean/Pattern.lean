import Lean
import Qq.Macro
import ExternalComputationsInLean.Syntax
import Mathlib.Data.Finset.Basic

open Lean Elab Meta Term Expr
open Qq


inductive ExprPattern
  | blank (id : MVarId)
  | blankOfType (id : MVarId) (t : ExprPattern)
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
  | .blank id => m!"ExprPattern.blank {id.name}"
  | .blankOfType id t => m!"ExprPattern.blankOfType {id.name} {toMessageData t}"
  | .bvar idx => m!"ExprPattern.bvar {idx}"
  | .fvar id => m!"ExprPattern.fvar"
  | .mvar id => m!"ExprPattern.mvar {id.name}"
  | .sort l => m!"ExprPattern.sort {l}"
  | .const declName us => m!"ExprPattern.const {declName} {us}"
  | .app f arg => m!"ExprPattern.app ({toMessageData f}) ({toMessageData arg})"
  | .lam binderName binderType body bi => m!"ExprPattern.lam {binderName} ({toMessageData binderType}) ({toMessageData body})"
  | .forallE binderName binderType body bi => m!"ExprPattern.forallE {binderName} ({toMessageData binderType}) ({toMessageData body})"
  | .letE binderName binderType value body nondep => m!"ExprPattern.letE {binderName} ({toMessageData binderType}) ({toMessageData value}) ({toMessageData body})"
  | .lit l => m!"ExprPattern.lit"
  | .proj structName idx e => m!"ExprPattern.proj {structName} {idx} ({toMessageData e})") ++ "\n"

instance : ToMessageData ExprPattern :=
  ⟨ExprPattern.toMessageData⟩

partial def ExprPattern.toString (e : ExprPattern) : String :=
  (match e with
  | .blank id => s!"ExprPattern.blank {id.name.toString}"
  | .blankOfType id t => s!"ExprPattern.blankOfType {id.name.toString} {toString t}"
  | .bvar idx => s!"ExprPattern.bvar {idx}"
  | .fvar id => s!"ExprPattern.fvar {id.name.toString}"
  | .mvar id => s!"ExprPattern.mvar {id.name.toString}"
  | .sort l => s!"ExprPattern.sort {l}"
  | .const declName us => s!"ExprPattern.const {declName} {us}"
  | .app f arg => s!"ExprPattern.app ({toString f}) ({toString arg})"
  | .lam binderName binderType body bi => s!"ExprPattern.lam {binderName} ({toString binderType}) ({toString body})"
  | .forallE binderName binderType body bi => s!"ExprPattern.forallE {binderName} ({toString binderType}) ({toString body})"
  | .letE binderName binderType value body nondep => s!"ExprPattern.letE {binderName} ({toString binderType}) ({toString value}) ({toString body})"
  | .lit l => match l with
    | .natVal n => s!"ExprPattern.lit (natVal {n})"
    | .strVal s => s!"ExprPattern.lit (strVal {s})"
  | .proj structName idx e => s!"ExprPattern.proj {structName} {idx} ({toString e})") ++ "\n"

instance : ToString ExprPattern :=
  ⟨ExprPattern.toString⟩

/- Converts an Expr into an ExprPattern; assumes synthetically added metavariables represent blanks to fill in -/
partial def toPattern (e : Expr) : MetaM ExprPattern := do
  match e with
  | .mvar _ => do
    match ← e.mvarId!.getKind with
    | MetavarKind.natural => return .mvar (e.mvarId!)
    | _ =>
      try
        let typ ← inferType e
        return .blankOfType (e.mvarId!) (← toPattern typ)
      catch _ =>
        return .blank (e.mvarId!)
  | .const n ls => do return .const n ls
  | .app f a => do return .app (← toPattern f) (← toPattern a)
  | .bvar i => do return .bvar i
  | .fvar id => do return .fvar id
  | .sort l => do return .sort l
  | .forallE n t b bi => do return .forallE n (← toPattern t) (← toPattern b) bi
  | .lam n t b bi => do return .lam n (← toPattern t) (← toPattern b) bi
  | .letE n t v b bi => do return .letE n (← toPattern t) (← toPattern v) (← toPattern b) bi
  | .lit l => do return .lit l
  | .proj s i e => do return .proj s i (← toPattern e)
  | .mdata _ e' => toPattern e' -- ignore metadata for now (IDK if there might be a future reason to keep it, but it'll just go out of scope anyway)

def ExprPattern.quote (e : ExprPattern) : Q(ExprPattern) :=
  match e with
  | .blank id => q(ExprPattern.blank $id)
  | .blankOfType id t =>
    let x : Q(ExprPattern) := t.quote
    q(ExprPattern.blankOfType $id $x)
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
partial def ExprPattern.isDefeq (e1 e2 : ExprPattern) : Bool :=
  match (e1, e2) with
  | (.blank _, .blank _) => true
  | (.blankOfType _ t1, .blankOfType _ t2) => t1.isDefeq t2
  | (.bvar i1, .bvar i2) => i1 == i2 -- TODO: check the logic around BVars (will indices be different even in equivalent patterns?)
  | (.fvar id1, .fvar id2) => id1 == id2
  | (.mvar _, .mvar _) => true -- Ideally matching the rest of the expression will ensure that enough constraints are placed on the metavariables for them to be equivalent
  | (.sort l1, .sort l2) => l1 == l2
  | (.const n1 ls1, .const n2 ls2) => n1 == n2 && ls1 == ls2
  | (.app f1 a1, .app f2 a2) => f1.isDefeq f2 && a1.isDefeq a2
  | (.lam n1 t1 b1 bi1, .lam n2 t2 b2 bi2) => n1 == n2 && t1.isDefeq t2 && b1.isDefeq b2 && bi1 == bi2
  | (.forallE n1 t1 b1 bi1, .forallE n2 t2 b2 bi2) => n1 == n2 && t1.isDefeq t2 && b1.isDefeq b2 && bi1 == bi2
  | (.letE n1 t1 v1 b1 bi1, .letE n2 t2 v2 b2 bi2) => n1 == n2 && t1.isDefeq t2 && v1.isDefeq v2 && b1.isDefeq b2 && bi1 == bi2
  | (.lit l1, .lit l2) => l1 == l2
  | (.proj s1 i1 e1, .proj s2 i2 e2) => s1 == s2 && i1 == i2 && e1.isDefeq e2
  | _ => false

/- Applies a function to every blank in the pattern, replacing it with the result -/
def ExprPattern.forEachBlank (e : ExprPattern) (fn : ExprPattern → ExprPattern) : ExprPattern :=
  match e with
  | .blank _ => fn e
  | .blankOfType id t => .blankOfType id (t.forEachBlank fn)
  | .app f a => .app (f.forEachBlank fn) (a.forEachBlank fn)
  | .lam n t b bi => .lam n (t.forEachBlank fn) (b.forEachBlank fn) bi
  | .forallE n t b bi => .forallE n (t.forEachBlank fn) (b.forEachBlank fn) bi
  | .letE n t v b bi => .letE n (t.forEachBlank fn) (v.forEachBlank fn) (b.forEachBlank fn) bi
  | .proj s i e => .proj s i (e.forEachBlank fn)
  | _ => e

/- Monadic version of forEachBlank -/
def ExprPattern.forEachBlankM [Monad m] (e : ExprPattern) (fn : ExprPattern → m ExprPattern) : m ExprPattern := do
  match e with
  | .blank _ => fn e
  | .blankOfType id t =>
    let t' ← t.forEachBlankM fn
    fn <| .blankOfType id t'
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
  | .blank id =>
    return [← elabContinuation e]
  | .blankOfType id t =>
    let typ ← inferType e
    -- logInfo m!"Matching blank of type: expected {typ}, pattern type {t}..."
    let _ ← t.match typ elabContinuation
    -- logInfo m!"...matched!"
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
  | .forallE n binder body bi =>
    if e.isForall then
      let res1 ← binder.match e.bindingDomain! elabContinuation
      let res2 ← body.match e.getForallBody elabContinuation
      return res1 ++ res2
    else
      throwError "Pattern does not match"
  | .mvar id =>
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

attribute [ext] MVarId
instance : DecidableEq MVarId :=
  fun a b => if h : a.name == b.name then .isTrue (by ext; simp_all) else .isFalse (by grind)

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

def ExprPattern.getBlanks (pat : ExprPattern) : List MVarId :=
  match pat with
  | .blank id => [id]
  | .blankOfType id t => id :: t.getBlanks
  | .app f a => f.getBlanks ++ a.getBlanks
  | .lam _ t b _ => t.getBlanks ++ b.getBlanks
  | .forallE _ t b _ => t.getBlanks ++ b.getBlanks
  | .letE _ t v b _ => t.getBlanks ++ v.getBlanks ++ b.getBlanks
  | .proj _ _ e => e.getBlanks
  | _ => []

def ExprPattern.fillBlank (pat : ExprPattern) (id : MVarId) (replacement : ExprPattern) : ExprPattern :=
  pat.forEachBlank fun e =>
    match e with
    | .blank bid => if bid == id then replacement else e
    | .blankOfType bid _ => if bid == id then replacement else e
    | _ => e

/- Makes an Expr from a pattern, given the Exprs that fill in the blanks. Assumes they all have the right type. -/
def ExprPattern.unifyToExpr (pat : ExprPattern) (blanks : Std.HashMap MVarId Expr) : MetaM Expr := do
  let filled ← pat.forEachBlankM fun e =>
    match e with
    | .blank id =>
      match blanks.get? id with
      | some expr => toPattern expr
      | none => throwError m!"No value provided for blank {id}"
    | .blankOfType id _ =>
      match blanks.get? id with
      | some expr => toPattern expr
      | none => throwError m!"No value provided for blank {id}"
    | _ => throwError "Internal error: non-blank passed to forEachBlankM"
  filled.toExpr

def fromSyntax (stx : Syntax) (expectedType? : Option Expr) : TermElabM ExprPattern := do
  let filled ← replaceUnknownIdents stx
  withoutModifyingElabMetaStateWithInfo do
    -- let e ← elabTerm filled expectedType?
    let ⟨e, _, _, _⟩ ← classifyMVars filled expectedType?
    toPattern (← instantiateMVars e)

def ExprPattern.isBlank (pat : ExprPattern) : Bool :=
  match pat with
  | .blank _ => true
  | .blankOfType _ _ => true
  | _ => false
