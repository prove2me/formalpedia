-- Prove2me | solution 1 for lean_workbook_plus_4779
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:05:37.940315+00:00
-- url     : https://prove2.me/submissions/7bb4b3a6-010b-4dcd-8b4a-49b65a55b748

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 * (b + c) / (b^2 + c^2) + b^2 * (c + a) / (c^2 + a^2) + c^2 * (a + b) / (a^2 + b^2) ≥ a + b + c)) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 1 , ?_⟩
  norm_num
