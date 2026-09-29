-- Prove2me | Theorems.Thm_lean_workbook_plus_64494
-- name    : lean_workbook_plus_64494
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3106a7b2-36ff-402c-8c55-0215d133b73f
-- statement:
--   $$ (a+b+c)(\frac{1}{a}+\frac{2}{b}+\frac{1}{c}) \leq 15$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64494 : ∀ a b c : ℝ, (a + b + c) * (1 / a + 2 / b + 1 / c) ≤ 15   :=  by sorry
