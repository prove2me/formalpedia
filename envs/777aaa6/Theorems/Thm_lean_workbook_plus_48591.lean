-- Prove2me | Theorems.Thm_lean_workbook_plus_48591
-- name    : lean_workbook_plus_48591
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/daa8f6d2-4896-4a18-98c0-5cc8fb6d2966
-- statement:
--   Multiplying the entire equation can lead us to cancel a lot of terms at the end. So $3S=3+3^2 + 3^3 + . . . + 3^{101}$ and subtracting both equations we get ... $S=\boxed{\frac{3^{101} -1}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48591  (s : ℝ)
  (h₀ : s = ∑ k in (Finset.range 101), (3^k)) :
  s = (3^101 - 1) / 2   :=  by sorry
