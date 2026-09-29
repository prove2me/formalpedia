-- Prove2me | solution 2 for sum_tangent_sampling_deviation_scales_le_single_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:26.281896+00:00
-- url     : https://prove2.me/submissions/1eb0da67-b5ca-4f3c-a6cc-511f8d1e7811

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
