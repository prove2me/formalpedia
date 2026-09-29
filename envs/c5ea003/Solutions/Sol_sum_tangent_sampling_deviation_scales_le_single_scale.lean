-- Prove2me | solution 1 for sum_tangent_sampling_deviation_scales_le_single_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:37.694316+00:00
-- url     : https://prove2.me/submissions/04f8a082-4826-4b28-a898-ca87ff76f039

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    (C₁ C₂ : ℝ) :
    0 < C₁ → 0 < C₂ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (β μ₀ : ℝ) (n r m : ℕ),
        tangentSamplingDeviationScale C₁ β μ₀ n r m +
            tangentSamplingDeviationScale C₂ β μ₀ n r m ≤
          tangentSamplingDeviationScale C β μ₀ n r m := by
  intro hC₁ hC₂
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro β μ₀ n r m
  unfold tangentSamplingDeviationScale
  ring_nf
  rfl
