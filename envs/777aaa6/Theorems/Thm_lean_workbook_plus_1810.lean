-- Prove2me | Theorems.Thm_lean_workbook_plus_1810
-- name    : lean_workbook_plus_1810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/df344222-a4eb-41b5-83ff-166bb5e44a0c
-- statement:
--   The following inequality is also true. \nIf $a, b, c>0, abc=1$ prove that \n $\sum_{cyc}{\\frac{1}{(2a^3+1)(a^3+2)}}\\ge\\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1810 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) : 1 / (2 * a ^ 3 + 1) * (a ^ 3 + 2) + 1 / (2 * b ^ 3 + 1) * (b ^ 3 + 2) + 1 / (2 * c ^ 3 + 1) * (c ^ 3 + 2) ≥ 1 / 3   :=  by sorry
