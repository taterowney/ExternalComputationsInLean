import Lean
import Mathlib.FieldTheory.Finite.Basic
-- import Mathlib.Data.Nat.Digits
import Std.Internal.Parsec
import Std.Internal.Parsec.String
import ExternalComputationsInLean.Elaborator



open Lean Meta Tactic Elab Meta Term Tactic Expr
open Std.Internal.Parsec Std.Internal.Parsec.String
open Std.Internal


class ParserContext where
  attrs : Std.HashMap String String := {}

instance : Inhabited ParserContext where
  default := { attrs := {} }


def CtxParser (α : Type) : Type := Parsec (String.Iterator × ParserContext) α

instance : Monad CtxParser where
  pure a := fun (it, ctx) => .success (it, ctx) a
  bind p f := fun (it, ctx) =>
    match p (it, ctx) with
    | .success (it', ctx') a => f a (it', ctx')
    | .error pos msg => .error pos msg

instance : Input (String.Iterator × ParserContext) Char String.Pos where
  pos it := it.1.pos
  next it := ⟨it.1.next, it.2⟩
  curr it := it.1.curr
  hasNext it := it.1.hasNext
  next' it := fun (h : it.1.hasNext) => ⟨it.1.next' h, it.2⟩
  curr' it := it.1.curr'


variable {α : Type}


def parseString (p : CtxParser α) (s : String) : Except String α :=
  match (p <* eof) ⟨s.mkIterator, default⟩ with
  | .success _ res => .ok res
  | .error _ msg => .error msg

partial def setAttr (key : String) (value : String) : CtxParser Unit := fun (it, ctx) =>
  .success (it, { ctx with attrs := ctx.attrs.insert key value }) ()

partial def getAttrs : CtxParser (Std.HashMap String String) := fun (it, ctx) =>
  .success (it, ctx) ctx.attrs

def pstring (s : String) : CtxParser String := fun (it, ctx) =>
  let substr := it.extract (it.forward s.length)
  if substr = s then
    .success (it.forward s.length, ctx) substr
  else
    .error ⟨it, ctx⟩ s!"expected: {s}"

@[inline]
def skipString (s : String) : CtxParser Unit := pstring s *> pure ()

@[inline]
def pchar (c : Char) : CtxParser Char := attempt do
  if (← any) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def skipChar (c : Char) : CtxParser Unit := pchar c *> pure ()

@[inline]
def digit : CtxParser Char := attempt do
  let c ← any
  if '0' ≤ c ∧ c ≤ '9' then return c else fail s!"digit expected"

@[inline]
private def digitToNat (b : Char) : Nat := b.toNat - '0'.toNat

@[inline]
private partial def digitsCore (acc : Nat) : CtxParser Nat := fun (it, ctx) =>
  /-
  With this design instead of combinators we can avoid allocating and branching over .success values
  all of the time.
  -/
  let ⟨res, it⟩ := go it acc
  .success ⟨it, ctx⟩ res
where
  go (it : String.Iterator) (acc : Nat) : (Nat × String.Iterator) :=
    if h : it.hasNext then
      let candidate := it.curr
      if '0' ≤ candidate ∧ candidate ≤ '9' then
        let digit := digitToNat candidate
        let acc := acc * 10 + digit
        go (it.next' h) acc
      else
        (acc, it)
    else
      (acc, it)

@[inline]
def digits : CtxParser Nat := do
  let d ← digit
  digitsCore (digitToNat d)

@[inline]
def hexDigit : CtxParser Char := attempt do
  let c ← any
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'f')
   ∨ ('A' ≤ c ∧ c ≤ 'F') then return c else fail s!"hex digit expected"

@[inline]
def asciiLetter : CtxParser Char := attempt do
  let c ← any
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then return c else fail s!"ASCII letter expected"

private partial def skipWs (it : String.Iterator) : String.Iterator :=
  if h : it.hasNext then
    let c := it.curr' h
    if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
      skipWs (it.next' h)
    else
      it
  else
   it

@[inline]
def ws : CtxParser Unit := fun (it, ctx) =>
  .success ⟨skipWs it, ctx⟩ ()

def take (n : Nat) : CtxParser String := fun (it, ctx) =>
  let substr := it.extract (it.forward n)
  if substr.length != n then
    .error ⟨it, ctx⟩ s!"expected: {n} codepoints"
  else
    .success ⟨it.forward n, ctx⟩ substr

-- TODO
def ExprPattern.isDefeq (e1 e2 : ExprPattern) : Bool := true
def ExprPattern.forEachBlank (e : ExprPattern) (f : ExprPattern → ExprPattern) : ExprPattern := e
def ExprPattern.forEachBlankM [Monad m] (e : ExprPattern) (f : ExprPattern → TermElabM ExprPattern) : m ExprPattern := pure e

def parserMethod (p : CtxParser ExprPattern) (pat : ExprPattern) (continuation : String → TermElabM ExprPattern) (s : String) : TermElabM ExprPattern := do
  let res := parseString p s
  match res with
  | .ok pat' =>
    if pat'.isDefeq pat then
      pat'.forEachBlankM (fun e => continuation e.toString)
    else
      throwError m!"Pattern does not match"
  | .error msg => throwError m!"Couldn't parse input: {msg}"

-- partial def matching_delimiters (start : String) (close : String) (continuation : CtxParser α) : CtxParser α := do
--   skipString start
--   addTag start
--   let result ← continuation
--   skipString close
--   return result

-- partial def word : CtxParser String := do
--     let mut s := ""
--     while true do
--       let next ← peek?
--       match next with
--       | some c' =>
--         if c'.isAlpha || c'.isDigit || c' == '_' then
--           s := s.push c'
--           skip
--         else
--           break
--       | none => break
--     let tags ← getTags
--     return s

-- #eval parseString (matching_delimiters "(*" "*)" (word)) "(*hello_this_is_a_test*)"
