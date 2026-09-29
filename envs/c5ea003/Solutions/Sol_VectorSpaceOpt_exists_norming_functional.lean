-- Prove2me | solution 1 for VectorSpaceOpt.exists_norming_functional
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:36.705728+00:00
-- url     : https://prove2.me/submissions/1075e6a8-9347-47b7-8f91-161bc6acab4e

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : X) (hx : x ≠ 0) :
    ∃ F : X →L[ℝ] ℝ, ‖F‖ = 1 ∧ VectorSpaceOpt_aligned x F := by
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector ℝ x (by simpa using hx)
  exact ⟨g, hg1, by simp [VectorSpaceOpt_aligned, hgx, hg1]⟩
