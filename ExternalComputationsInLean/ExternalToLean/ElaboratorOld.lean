import Lean
import Lean.Meta.Tactic.TryThis
import Qq.Macro
import Mathlib.Data.Real.Basic
import ExternalComputationsInLean.Utils.Pattern


open Lean Meta Tactic Elab Meta Term Tactic Expr Lean.Meta.Tactic.TryThis
open Qq
open ExprPattern


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
    catch e =>
      -- logInfo m!"Elaborator {i} did not match: {e.toMessageData}"
      continue
  throwError m!"No matching elaboration found for expression: {e}"

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
      let mut ⟨pat, _, _, _⟩ ← classifyMVars type_stx none
      pat ← instantiateMVars pat
      let e ← toPattern pat
      let quoted := e.quote

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
