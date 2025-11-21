import ExternalComputationsInLean.IntervalArith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Leibniz
import Mathlib.Data.Real.GoldenRatio



set_option warn.sorry false
example : (2:ℝ) ≥ 1 :=
  Classical.byContradiction (
      let f1 : Real := 1;
      let r1 : Real := 2;
      let p1 := f1 ≤ r1;
      let s1 := ¬p1;
      let f2 : Real := 2;
      let i1 := Set.Icc f2 f2;
      let p2 := r1 ∈ i1;
      let t1 : p2 := by grind;
      let l2 : s1 -> p2 :=
      fun h0 =>
        t1;
      let l1 : s1 -> «False» := fun h0 => let h1 := h0; let h2 := l2 h0; by grind;
      l1
  )



-- example : (2:Real) ≥ 1:= by
--   gappa



-- Bounds on square roots
example : √2 * 1000 ≤ 1415 := by
  gappa
  -- canonical

example : √3 * 1024 ≤ 1774 := by
  gappa

-- Bounding the golden ratio
open goldenRatio in
example : 16 ≤ φ * 10 ∧ φ * 10 ≤ 17 := by
  unfold goldenRatio
  constructor
  · suffices (1 + √5) / 2 * 10 ≥ 16 by exact this
    gappa
  gappa


-- variable (y : ℝ)

-- -- Bounds on a quadratic expression
-- example : y >= 0 ∧ y <= 1 → y * (1-y) * 3 <= 1 := by
--   gappa
