-- Prove2me | Theorems.Thm_lean_workbook_plus_16358
-- name    : lean_workbook_plus_16358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e3d10103-c224-4a5f-bb65-7e764601b16f
-- statement:
--   a, b are positive reals such that \\(a+b = 1\\) . Prove that \n\\(\\frac{1}{3}\\leq \\frac{a^{2}}{a+1}+\\frac{b^{2}}{b+1}< \\frac{1}{2}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16358 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a + b = 1) : 1 / 3 ≤ a ^ 2 / (a + 1) + b ^ 2 / (b + 1) ∧ a ^ 2 / (a + 1) + b ^ 2 / (b + 1) < 1 / 2   :=  by sorry
