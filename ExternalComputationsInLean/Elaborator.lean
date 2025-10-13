import Lean
import Lean.Meta.Tactic.TryThis
import Qq.Macro

import Mathlib.Data.Real.Basic


open Lean Meta Tactic Elab Meta Term Tactic Expr Lean.Meta.Tactic.TryThis
open Qq


partial def collectUnknownIdents (stx : Syntax) : TermElabM (Array Syntax) := do
  let mut bad := #[]
  if stx.isIdent then
    let tryResolve : TermElabM Unit := do
      let res ← Term.resolveId? stx
      if (!res.isSome) then
        throwError "Unresolved identifier"
      pure ()
    try
      tryResolve
    catch _ =>
      bad := bad.push stx
  for c in stx.getArgs do
    bad := bad ++ (← collectUnknownIdents c)
  return bad


partial def replaceUnknownIdents (stx : Syntax) : TermElabM (Syntax) := do
  if stx.isIdent then
    let tryResolve : TermElabM Syntax := do
      let res ← Term.resolveId? stx
      if (!res.isSome) then
        throwError "Unresolved identifier"
      pure stx
    try
      return (← tryResolve)
    catch _ =>
      return Lean.mkHole stx
  let mut out := stx
  for (c, i) in List.zipIdx <| stx.getArgs.toList do
    out := out.setArg i (← replaceUnknownIdents c)
  return out

-- gotta make this because you cant go back and find the context/types of metavariables later
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
  | .blank id => m!"ExprPattern.blank {id}"
  | .blankOfType id t => m!"ExprPattern.blankOfType {id} {toMessageData t}"
  | .bvar idx => m!"ExprPattern.bvar {idx}"
  | .fvar id => m!"ExprPattern.fvar"
  | .mvar id => m!"ExprPattern.mvar"
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
  | _ => do return .blank (← mkFreshMVarId)

def quoteExprPattern (e : ExprPattern) : Q(ExprPattern) :=
  match e with
  | .blank id => q(ExprPattern.blank $id)
  | .blankOfType id t =>
    let x : Q(ExprPattern) := quoteExprPattern t
    q(ExprPattern.blankOfType $id $x)
  | .bvar i => q(ExprPattern.bvar $i)
  | .fvar id => q(ExprPattern.fvar $id)
  | .mvar id => q(ExprPattern.mvar $id)
  | .sort l => q(ExprPattern.sort $l)
  | .const n ls => q(ExprPattern.const $n $ls)
  | .app f a =>
    let x : Q(ExprPattern) := quoteExprPattern f
    let y : Q(ExprPattern) := quoteExprPattern a
    q(ExprPattern.app $x $y)
  | .lam n t b bi =>
    let x : Q(ExprPattern) := quoteExprPattern t
    let y : Q(ExprPattern) := quoteExprPattern b
    q(ExprPattern.lam $n $x $y $bi)
  | .forallE n t b bi =>
    let x : Q(ExprPattern) := quoteExprPattern t
    let y : Q(ExprPattern) := quoteExprPattern b
    q(ExprPattern.forallE $n $x $y $bi)
  | .letE n t v b bi =>
    let x : Q(ExprPattern) := quoteExprPattern t
    let y : Q(ExprPattern) := quoteExprPattern v
    let z : Q(ExprPattern) := quoteExprPattern b
    q(ExprPattern.letE $n $x $y $z $bi)
  | .lit l => q(ExprPattern.lit $l)
  | .proj s i e =>
    let x : Q(ExprPattern) := quoteExprPattern e
    q(ExprPattern.proj $s $i $x)



structure PythonElabContext where
  pattern : ExprPattern
  format_fn : Expr × List String → MetaM String

instance : ToString PythonElabContext where
  toString ctx := s!"PythonElabContext(pattern={ctx.pattern}"



def quote_expr (e : Expr) : TermElabM Expr := do
  return q($e)

def print_equality (e : Expr × List String) : MetaM String := do
  if e.2.length != 2 then
    throwError "Expected exactly two holes"
  return s!"{e.2[0]!} = {e.2[1]!}"

def print_real (e : Expr × List String) : MetaM String := do
  match e.1 with
  | .app x y =>
    -- logInfo m!"Real triggered: x is {x}"
    if x.appFn!.appArg! == Lean.mkConst ``Real then
      return s!"{x.appArg!}.0"
    else
      throwError "not a real"
  | .fvar id =>
    return s!"{← id.getUserName}"
  | _ => throwError "Expected a real literal"

def print_float (e : Expr × List String) : MetaM String := do
  match e.1 with
  | .app x y =>
    if x.appFn!.appArg! == Lean.mkConst ``Float32 then
      return s!"{x.appArg!}"
    else
      throwError m!"{x} is not a float"
  | .fvar id =>
    return s!"{← id.getUserName}"
  | _ => throwError "Expected a float literal"

def print_nat (e : Expr × List String) : MetaM String := do
  match e.1 with
  | .app x y =>
    if x.appFn!.appArg! == Lean.mkConst ``Nat then
      return s!"{x.appArg!}"
    else
      throwError "not a nat"
  | .fvar id =>
    return s!"{← id.getUserName}"
  | _ => throwError "Expected a nat literal"

def print_int (e : Expr × List String) : MetaM String := do
  match e.1 with
  | .app x y =>
    if x.appFn!.appArg! == Lean.mkConst ``Int then
      return s!"{x.appArg!}"
    else
      throwError "not an int"
  | .fvar id =>
    return s!"{← id.getUserName}"
  | _ => throwError "Expected an int literal"



-- Returns formatted bits of metavariable holes left in the expression pattern
partial def matchAndFormat (pat : ExprPattern) (e : Expr) (elabContinuation : Expr → MetaM String := (fun x => pure "Inner")) : MetaM (List String) := do
  match pat with
  | .blank id =>
    return [← elabContinuation e]
  | .blankOfType id t =>
    -- logInfo m!"Internal hole triggered: type {t}"
    let typ ← inferType e
    -- logInfo m!"target type is {typ}"
    let _ ← matchAndFormat t typ elabContinuation
    return [← elabContinuation e]
  | .const c _ =>
    if e.isConstOf c then
      return []
    else
      throwError "Pattern does not match"
  | .sort l =>
    if e.isSort then
      -- logInfo m!"e is sort with level {e.sortLevel!}"
      if l.isMVar then -- Hacky solution for now; should make this a real pattern
        -- logInfo m!"level is metavariable, accepting"
        return []
      else if l == e.sortLevel! then
        return []
      else
        throwError "Pattern does not match"
    else
      throwError "Pattern does not match"
  | .app f arg =>
    if h : e.isApp then
      return (← matchAndFormat f (e.appFn h) elabContinuation) ++ (← matchAndFormat arg e.appArg! elabContinuation)
    else
      throwError "Pattern does not match"
  | .lit l =>
    if e.isLit && l == e.litValue! then
      return []
    else
      throwError "Pattern does not match"
  | .forallE n binder body bi =>
    if e.isForall then
      let res1 ← matchAndFormat binder e.bindingDomain! elabContinuation
      let res2 ← matchAndFormat body e.getForallBody elabContinuation
      return res1 ++ res2
    else
      throwError "Pattern does not match"
  | .mvar id =>
    return []
  | _ => throwError "matchAndFormat: this pattern is not supported"


partial def doPythonElaboration (elaborators : List PythonElabContext) (e : Expr) : MetaM String := do
  -- logInfo m!"Doing elaboration on expression: {e}"
  for ⟨ctx, i⟩ in List.zipIdx elaborators do
    -- logInfo m!"Trying elaborator {i}: {ctx}"
    let pat := ctx.pattern
    let format_fn := ctx.format_fn

    try
      match pat with
      | .blank id =>
        return ← format_fn (e, [])
      | .blankOfType id t => do
        -- logInfo m!"Blank triggered: type {t} with target type {← inferType e}"
        try
          let matchRes ← matchAndFormat t (← inferType e) (fun e => doPythonElaboration elaborators e) -- TODO: do we want a different continuation here (i.e. just match anything eagerly)?
          return ← format_fn (e, [])
        catch _ =>
          throwError "Pattern does not match type"
      | .mvar id =>
        return ← format_fn (e, [])
      | _ => do
        let res ← matchAndFormat pat e (fun e => doPythonElaboration elaborators e)
        return ← format_fn (e, res)
    catch _ =>
      continue
  throwError m!"No matching elaboration found for expression: {e}"

/-- Elaborate `stx` in the current `MVarContext`. If given, the `expectedType` will be used to help
elaboration and then a `TypeMismatchError` will be thrown if the elaborated type doesn't match.  -/
def TermElabM.elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TermElabM Expr := do
  let e ← Lean.Elab.Term.elabTerm stx expectedType? mayPostpone
  -- We do use `Term.ensureExpectedType` because we don't want coercions being inserted here.
  match expectedType? with
  | none => return e
  | some expectedType =>
    let eType ← inferType e
    -- We allow synthetic opaque metavars to be assigned in the following step since the `isDefEq` is not really
    -- part of the elaboration, but part of the tactic. See issue #492
    unless (← withAssignableSyntheticOpaque <| isDefEq eType expectedType) do
      Term.throwTypeMismatchError none expectedType eType e
    return e

/--
Execute `k`, and collect new "holes" in the resulting expression.

* `parentTag` and `tagSuffix` are used to tag untagged goals with `Lean.Elab.Tactic.tagUntaggedGoals`.
* If `allowNaturalHoles` is true, then `_`'s are allowed and create new goals.
-/
def TermElabM.withCollectingNewGoalsFrom (k : TermElabM Expr) (parentTag : Name) (tagSuffix : Name) (allowNaturalHoles := false) : TermElabM (Expr × List MVarId) :=
  /-
  When `allowNaturalHoles = true`, unassigned holes should become new metavariables, including `_`s.
  Thus, we set `holesAsSyntheticOpaque` to true if it is not already set to `true`.
  See issue #1681. We have the tactic
  ```
  `refine' (fun x => _)
  ```
  If we create a natural metavariable `?m` for `_` with type `Nat`, then when we try to abstract `x`,
  a new metavariable `?n` with type `Nat -> Nat` is created, and we assign `?m := ?n x`,
  and the resulting term is `fun x => ?n x`. Then, `getMVarsNoDelayed` would return `?n` as a new goal
  which would be confusing since it has type `Nat -> Nat`.
  -/
  if allowNaturalHoles then
    withTheReader Term.Context (fun ctx => { ctx with holesAsSyntheticOpaque := ctx.holesAsSyntheticOpaque || allowNaturalHoles }) do
      /-
      We also enable the assignment of synthetic metavariables, otherwise we will fail to
      elaborate terms such as `f _ x` where `f : (α : Type) → α → α` and `x : A`.

      IMPORTANT: This is not a perfect solution. For example, `isDefEq` will be able assign metavariables associated with `by ...`.
      This should not be an immediate problem since this feature is only used to implement `refine'`. If it becomes
      an issue in practice, we should add a new kind of opaque metavariable for `refine'`, and mark the holes created using `_`
      with it, and have a flag that allows us to assign this kind of metavariable, but prevents us from assigning metavariables
      created by the `by ...` notation.
      -/
      withAssignableSyntheticOpaque go
  else
    go
where
  go := do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let val ← k
    let newMVarIds ← getMVarsNoDelayed val
    /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
    let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
    /- Filter out all mvars that were created prior to `k`. -/
    let newMVarIds ← filterOldMVars newMVarIds mvarCounterSaved
    /- If `allowNaturalHoles := false`, all natural mvarIds must be assigned.
    Passing this guard ensures that `newMVarIds` does not contain unassigned natural mvars. -/
    unless allowNaturalHoles do
      let naturalMVarIds ← newMVarIds.filterM fun mvarId => return (← mvarId.getKind).isNatural
      -- logUnassignedAndAbort naturalMVarIds
    /-
    We sort the new metavariable ids by index to ensure the new goals are ordered using the order the metavariables have been created.
    See issue #1682.
    Potential problem: if elaboration of subterms is delayed the order the new metavariables are created may not match the order they
    appear in the `.lean` file. We should tell users to prefer tagged goals.
    -/
    let newMVarIds ← sortMVarIdsByIndex newMVarIds.toList
    -- tagUntaggedGoals parentTag tagSuffix newMVarIds
    return (val, newMVarIds)


def elabTermWithHoles (stx : Syntax) (expectedType? : Option Expr) (tagSuffix : Name) (allowNaturalHoles := false) : TermElabM (Expr × List MVarId) := do
  TermElabM.withCollectingNewGoalsFrom (TermElabM.elabTermEnsuringType stx expectedType?) (`anonymous) tagSuffix allowNaturalHoles


/-- Elaborate `stx` and classify metavariables:
* `holes` are the mvars created directly from `_` / `?m` holes
* `synth` are synthetic (typeclass/coercion/tactic/postponed) mvars
* `natural` are remaining “natural” mvars -/
def classifyMVars (stx : Syntax) (expected? : Option Expr := none)
    : TermElabM (Expr × Array MVarId × Array (MVarId × Option Term.SyntheticMVarKind) × Array MVarId) := do
  -- tagSuffix is used to tag unnamed goal mvars; allow natural `_` holes
  let tag := Name.str .anonymous "user_hole"
  let (e, holeMVars) ← elabTermWithHoles stx expected? tag (allowNaturalHoles := true)

  -- collect *all* mvars that still occur in the term
  let all ← Meta.getMVars e

  -- fast set for membership
  let holeSet := holeMVars.foldl (init := ({} : Std.HashSet MVarId)) (·.insert ·)

  -- partition the rest using SyntheticMVarDecl (TC/coercion/tactic/postponed info)
  let mut synth : Array (MVarId × Option Term.SyntheticMVarKind) := #[]
  let mut natural : Array MVarId := #[]
  for m in all do
    if holeSet.contains m then
      continue
    else
      match (← Term.getSyntheticMVarDecl? m) with
      | some d => synth := synth.push (m, some d.kind)
      | none   =>
        -- if it was created as a synthetic-opaque goal (?m / tactic goal) we still mark it "synth"
        match (← m.getKind) with
        | MetavarKind.syntheticOpaque => synth := synth.push (m, none)
        | _                           => natural := natural.push m
  pure (e, holeMVars.toArray, synth, natural)

-- def classifyFromTerm (stx : Syntax) (expected? : Option Expr := none)
--     : TermElabM (Expr × List MVarId × Array (MVarId × Option Term.SyntheticMVarKind) × Array MVarId) := do
--   Tactic.runTermElab (classifyMVars stx expected?) (mayPostpone := true)

-- #check Tactic.runTermElab

syntax (name := python_elab) "py_elab " term " ==> " term : term

@[term_elab python_elab]
def python_elab_impl : TermElab := fun stx expectedType? => do
  let type_stx ← replaceUnknownIdents stx[1]
  -- logInfo m!"Type stx after replacing unknown idents: {type_stx}"
  let format_fn ← elabTerm stx[3] (some q(Expr × List String → MetaM String))

  return ← withoutModifyingElabMetaStateWithInfo do
    try
      -- let mut pat ← elabTerm type_stx none
      -- let mut ⟨pat, holes⟩ ← elabTermWithHoles type_stx none `pythonElab true
      let mut ⟨pat, holes, synth, natural⟩ ← classifyMVars type_stx none
      pat ← instantiateMVars pat


      let e ← toPattern pat
      let quoted := quoteExprPattern e

      let out : Expr := (.app (.app (mkConst ``PythonElabContext.mk) quoted) format_fn)
      return out

    catch _ =>
      -- let id ← mkFreshMVarId
      -- return q(ExprPattern.blank $id)
      throwError "Failed to convert to pattern"




-- TODO: recreate metavariable coupling, handle level mvars
-- #eval py_elab (x → y) ==> fun e => do
--   return s!"{e.2[0]!} + {e.2[1]!}"



variable (x : Real)


-- TODO: :(
-- #eval do
--   let and := py_elab (x ∧ y) ==> fun e => do
--     return s!"{e.2[0]!} ∧ {e.2[1]!}"
--   let eq := py_elab (x = y) ==> print_equality
--   let real := py_elab ((x : Real)) ==> print_real
--   let forall_ := py_elab (∀ (x : Nat), y) ==> fun e => do
--     return s!"{e.2[0]!} + {e.2[1]!}"
--   -- let h ← doPythonElaboration [and, real, eq] (q((1 : Real)=1) : Expr)
--   let h ← doPythonElaboration [and, real, eq, forall_] (q(∀ (x : Nat), x=1) : Expr)

--   logInfo m!"{h}"
