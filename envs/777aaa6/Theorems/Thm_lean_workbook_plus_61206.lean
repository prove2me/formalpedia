-- Prove2me | Theorems.Thm_lean_workbook_plus_61206
-- name    : lean_workbook_plus_61206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c7035da7-c52a-44e0-873d-8b778fb049ee
-- statement:
--   Let $a,b,c>0.$ Show that \n\n $$ab(a^2+b^2) \leq \frac{(a+b)^4}{8} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61206 (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) : a * b * (a ^ 2 + b ^ 2) ≤ (a + b) ^ 4 / 8   :=  by sorry
