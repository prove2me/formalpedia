-- Prove2me | Theorems.Thm_lean_workbook_plus_72145
-- name    : lean_workbook_plus_72145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4a6f28b3-473d-42d9-8fc1-f56264b75c0c
-- statement:
--   Show that $cd\leq\frac{(c+d)^2}{4}$ and $ab\leq\frac{(a+b)^2}{4}$ using the AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72145 (a b c d : ℝ) : a * b ≤ (a + b) ^ 2 / 4 ∧ c * d ≤ (c + d) ^ 2 / 4   :=  by sorry
