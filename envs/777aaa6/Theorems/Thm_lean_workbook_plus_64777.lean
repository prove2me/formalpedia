-- Prove2me | Theorems.Thm_lean_workbook_plus_64777
-- name    : lean_workbook_plus_64777
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/47cfb785-3438-4092-a75f-e298b29fa7a8
-- statement:
--   Prove that $cosA.cosB+cosB.cosC+cosC.cosA\leq \\frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64777 : ∀ A B C : ℝ, cos A * cos B + cos B * cos C + cos C * cos A ≤ 3 / 4   :=  by sorry
