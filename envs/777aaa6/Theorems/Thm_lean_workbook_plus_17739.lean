-- Prove2me | Theorems.Thm_lean_workbook_plus_17739
-- name    : lean_workbook_plus_17739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/dce884d2-1923-4127-9359-5df4a6bc2945
-- statement:
--   With the constraint $4a + 2\pi r = 4$ , we have $a = 1 - \tfrac{\pi}{2}r$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17739 (a r : ℝ) (h₁ : 4 * a + 2 * π * r = 4) : a = 1 - π / 2 * r   :=  by sorry
