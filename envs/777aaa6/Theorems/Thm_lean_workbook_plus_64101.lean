-- Prove2me | Theorems.Thm_lean_workbook_plus_64101
-- name    : lean_workbook_plus_64101
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b74906f3-ac1a-4ecf-b407-ee8620de6c52
-- statement:
--   At the end of one month, because you're taking out $ \frac{1}{4} $ of the original water, you'll have $ \frac{3}{4} $ of it left. In volume, that'll be $ 150000*\frac{3}{4} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64101  (x : ℝ)
  (h₀ : x = 150000) :
  3/4 * x = 150000 * 3/4   :=  by sorry
