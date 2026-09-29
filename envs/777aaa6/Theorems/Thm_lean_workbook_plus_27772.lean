-- Prove2me | Theorems.Thm_lean_workbook_plus_27772
-- name    : lean_workbook_plus_27772
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b3662573-ead7-48f5-984b-5fb48bed9688
-- statement:
--   The domain of the definition is: $t\in\left(-\infty,-\frac{3}{2}\right)\cup\left(\frac{3}{2},\infty\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27772 (t : ℝ) : (t < -3/2 ∨ 3/2 < t) → 0 < (t^2 - 9/4)   :=  by sorry
