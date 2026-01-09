import ExternalComputationsInLean.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Bitwise

open Lean Meta Elab Meta Term Expr Command









external Rocq_language where
  "True" <==> True
  "False" <==> False
  x "/\\" y <==> x ∧ y
  x "\\/" y <==> x ∨ y
  "not" x <==> ¬x
  x "->" y <==> x → y
  "let" $x ":=" y "in" z <==> let x := y; z
  "fun" $x "=>" y <==> fun x => y
  "-" x <==> - (Int.ofNat x)
  "+" x <==> Int.ofNat x
  "(" x ")" <==> x
  "Gappa.Gappa_definitions.makepairF" x y <==> Set.Icc (x:Int) (y:Int)
  "Gappa.Gappa_definitions.BND" x y <==> (x : Int) ∈ (y : Set Int)

#eval process Rocq_language
"let interval := Gappa.Gappa_definitions.makepairF (-1) (+2) in
(not Gappa.Gappa_definitions.BND (+0) interval) /\\ True"













external C_arithmetic where
  "int" $functionName "(" "int" $paramName ")" "{" body "}" <==>
    let functionName := ();
    fun (paramName : Int32) => body
  "int" $varname "=" x ";" rest <==> let varname : Int32 := x; rest
  x "+" y <==> (x:Int32) + (y:Int32)
  x "-" y <==> (x:Int32) - (y:Int32)
  x "*" y <==> (x:Int32) * (y:Int32)
  x "/" y <==> (x:Int32) / (y:Int32)
  x "%" y <==> (x:Int32) % (y:Int32)
  x "<<" y <==> (x:Int32) <<< (y:Int32)
  x ">>" y <==> (x:Int32) >>> (y:Int32)
  "(" x ")" <==> Int32.ofNat x
  "return" x ";" <==> x



def code1 := process C_arithmetic
"int x = (10);
int y = (3);
int z = x << y + x >> y;
z % (7)"

#print code1

example : code1 = 6 := by decide



def code2 := process C_arithmetic
"int main (int x) {
  int y = x << (2);
  return y+(1);
}"

#print code2



example (x : Int32) (hx : x < 2^30 - 1) : code2 x = 4*x + 1 := by
  simp [code2]
  sorry
