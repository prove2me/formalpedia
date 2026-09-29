-- Prove2me | solution 1 for lean_workbook_plus_70193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:29.526516+00:00
-- url     : https://prove2.me/submissions/243b5c45-ff37-43e6-9e50-417a287861c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1 := by
  refine ⟨fun k => (2:ℝ)^(k-1)*r, ?_, ?_⟩
  · norm_num
  · intro k
    norm_num
