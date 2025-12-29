import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

-- import Canonical

variable {N : ℕ}

open Function Metric Set

open Metric MeasureTheory


#check EuclideanSpace ℝ (Fin N) -- This is ℝ^N with the usual inner product and norm

#check IsCompact -- Compactness predicate on sets in topological spaces

#check IsFixedPt -- Fixed point predicate for functions from a type to itself

#check frontier -- Boundary of a set

-- #check lintegral_image_eq_lintegral_abs_det_fderiv_mul

#check volume

#check Real.volume_pi_closedBall

#check lipschitzWith_of_nnnorm_deriv_le
#check ContDiffOn
#check lt_min_iff

abbrev Rn := EuclideanSpace ℝ (Fin N)

-- instance : Nontrivial (EuclideanSpace ℝ (Fin N)) := ⟨0, 1, zero_ne_one⟩

-- set_option maxHeartbeats 2000000

lemma not_exists_continuous_retraction_sphere (x : EuclideanSpace ℝ (Fin N)) :
  ¬ ∃ (r : Rn → Rn)
      (h_range : range r ⊆ frontier (closedBall x 1 : Set Rn))
      (h_c1 : ContDiffOn ℝ 1 r (closedBall x 1 : Set Rn)),
      (∀ (y : closedBall x 1), dist x y = 1 → IsFixedPt r y) := by
  by_contra h
  rcases h with ⟨r, h_range, h_c1, h_fixed⟩

  -- let r_restricted : closedBall x 1 → closedBall x 1 := fun y => ⟨r y, h_range ⟨y, by sorry⟩⟩

  let g : Real → Rn → Rn :=
    fun t y => (1 - t) • (y) + t • (r y)

  let h : Rn → Rn := fun y => ((r y) : Rn) - (y : Rn)

  have is_lipschitz : ∃ (M : Real), 0 < M ∧ ∀ x₁ ∈ (closedBall x 1), ∀ x₂ ∈ (closedBall x 1), dist (h x₁) (h x₂) ≤ M * dist x₁ x₂  := by
    have h'_bounded : ∃ M, ∀ y ∈ (closedBall x 1), ‖(fderiv ℝ h) y‖ ≤ M := sorry
    obtain ⟨M, h'_bound⟩ := h'_bounded

    have : LipschitzWith M.toNNReal h := sorry -- lipschitzWith_of_nnnorm_deriv_le
    use M
    sorry

  obtain ⟨M, h_pos,  h_lipschitz⟩ := is_lipschitz

  have is_injective : ∀ t ∈ Ico (0 : Real) (min 1 (1 / M)), InjOn (g t) (ball x 1) := by
    by_contra h; push_neg at h
    rcases h with ⟨t, ht, h_not_inj⟩
    unfold InjOn at h_not_inj; push_neg at h_not_inj
    rcases h_not_inj with ⟨x₁, hx₁, x₂, hx₂, h_coincide, h_neq⟩
    have : t * M < 1 := by
      have : t * M < (1 / M) * M := mul_lt_mul_of_pos_right (lt_min_iff.mp (mem_Ico.mp ht).2 |>.2) (sorry)
      rw [one_div] at this
      grind only [= subset_def, = mem_Ico, cases Or]
    have : dist x₁ x₂ < dist x₁ x₂ := by
      calc
        dist x₁ x₂ = t * dist (h x₁) (h x₂) := by
          sorry
        _ ≤ t * (M * dist x₁ x₂) := mul_le_mul_of_nonneg_left (h_lipschitz x₁ sorry x₂ sorry) (mem_Ico.mp ht).1
        _ < 1 * dist x₁ x₂ := by
          rw [← mul_assoc]
          exact mul_lt_mul_of_pos_right this (dist_pos.mpr h_neq)
        _ = dist x₁ x₂ := by rw [one_mul]
    exact lt_irrefl (dist x₁ x₂) this

  -- Derivative of g
  let g' : ℝ → Rn → Rn →L[ℝ] Rn := fun t => fderiv ℝ (g t)

  have jacobian_nonzero : ∃ (t0 : Real), ∀ t ∈ Ico 0 t0, ∀ y ∈ (ball x 1), HasFDerivWithinAt (g t) (g' t y) (ball x 1) y := by sorry
  obtain ⟨t0, h_jacobian⟩ := jacobian_nonzero

  have g_preserves_ball : ∀ t ∈ Ico 0 t0, (g t) '' (ball x 1) = ball x 1 := by
    intro t ht
    have image_open : IsOpen ( (g t) '' (ball x 1)) := by sorry
    have image_constrained : (g t) '' (ball x 1) ⊆ ball x 1 := by sorry
    have : ball x 1 ⊆ (g t) '' (ball x 1) := by
      have : ∀ y ∈ frontier ((g t) '' (ball x 1)), y ∈ frontier (ball x 1) := by
        intro y hy
        by_contra h
        sorry
      sorry

    sorry


  have cursed_integral : ∀ t ∈ Ico 0 (min t0 (min 1 (1/M))),
    volume (closedBall x 1) = ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(g' t y).det| ∂(volume) := by
    intro t ht
    have in_t0 : t ∈ Ico 0 t0 := by
      simp only [mem_Ico]
      constructor
      · exact (mem_Ico.mp ht).1
      exact (lt_min_iff.mp (mem_Ico.mp ht).2).1
    have in_inj : t ∈ Ico 0 (min 1 (1 / M)) := by
      simp only [mem_Ico]
      constructor
      · exact (mem_Ico.mp ht).1
      exact (lt_min_iff.mp (mem_Ico.mp ht).2).2
    calc
      volume (Metric.closedBall x 1) = volume (Metric.ball x 1) := by
        rw [Measure.addHaar_closedBall_center,
          Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
          ← Measure.addHaar_ball_center]
      _ = volume ((g t) '' (ball x 1)) := by rw [g_preserves_ball t in_t0]
      _ = ∫⁻ y in (g t) '' (ball x 1), (fun y => 1) y ∂(volume) := by exact Eq.symm (setLIntegral_one (g t '' ball x 1))
      _ = ∫⁻ y in (ball x 1), ENNReal.ofReal |(g' t y).det| * 1 ∂(volume) := by
          apply lintegral_image_eq_lintegral_abs_det_fderiv_mul (E := Rn) volume (measurableSet_ball (x := x) (ε := 1)) (h_jacobian t in_t0) (is_injective t in_inj) (fun y => 1) -- Have to specify the lemmas manually or else tactic execution freezes for some reason...
      _ = ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(g' t y).det| ∂(volume) := by
        simp only [mul_one]
        sorry


  have integral_is_linear : ∀ t ∈ Icc 0 1,
    ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(g' t y).det| ∂(volume) = (ENNReal.ofReal t) * ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(fderiv ℝ (fun y => (g t y) - y) y).det| ∂(volume) + volume (closedBall x 1) := by
    intro t ht
    calc
      ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(g' t y).det| ∂(volume)
        = ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(t • fderiv ℝ (fun y => (g t y) - y) y + fderiv ℝ (fun (y : Rn) => y) y).det| ∂(volume) := by
          congr
          simp only [fderiv_id']
          sorry
      _ = ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(t • fderiv ℝ (fun y => (g t y) - y) y).det| + 1 ∂(volume) := by sorry
      _ = (ENNReal.ofReal t) * ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(fderiv ℝ (fun y => (g t y) - y) y).det| ∂(volume) + volume (closedBall x 1) := by sorry

  let r' := fderiv ℝ r
  have integral_is_constant :
    ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(r' y).det| ∂(volume) = volume (closedBall x 1) := by sorry

  have r'_singular : ∀ y ∈ closedBall x 1, (r' y).det = 0 := by
    have : ∀ y ∈ closedBall x 1, dist x (r y) = 1 := by
      intro y hy
      sorry
    sorry

  have final_contradiction :
    volume (closedBall x 1) = 0 := by
    calc
      volume (closedBall x 1)
          = ∫⁻ y in (closedBall x 1), ENNReal.ofReal |(r' y).det| ∂(volume) := by rw [integral_is_constant]
      _ = ∫⁻ y in (closedBall x 1), 0 ∂(volume) := by sorry
      _ = 0 := lintegral_zero

  have : ENNReal.ofReal ((2) ^ N) = 0 := by
    rw [← mul_one 2]
    -- Real.volume_pi_closedBall will be helpful; use final_contradiction
    sorry

  have : ENNReal.ofReal ((2 : Real) ^ N) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Nat.ofNat_pos, pow_pos]

  contradiction

theorem brouwer {f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
  (hf : Continuous f) :
  ∃ x : EuclideanSpace ℝ (Fin N), IsFixedPt f x := by sorry
