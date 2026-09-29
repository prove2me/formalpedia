-- Prove2me | Theorems.Thm_lean_workbook_plus_40785
-- name    : lean_workbook_plus_40785
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0540bc6a-3805-42b8-9c73-a54c4a5306f6
-- statement:
--   WE know that $ \sqrt{a^{2}+ab+b^{2}}\geq\frac{\sqrt{3}}{2}(a+b)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40785 (a b : ℝ) : Real.sqrt (a ^ 2 + a * b + b ^ 2) ≥ Real.sqrt 3 / 2 * (a + b)   :=  by sorry
