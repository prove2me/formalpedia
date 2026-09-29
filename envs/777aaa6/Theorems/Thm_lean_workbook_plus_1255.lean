-- Prove2me | Theorems.Thm_lean_workbook_plus_1255
-- name    : lean_workbook_plus_1255
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0a2ce7ef-145b-414c-bd1f-e48e4bd7cdf2
-- statement:
--   Let a, b, c be three positive real numbers such that $ a+b+c=3 $. Prove that $\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2} \ge \frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1255 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) ≥ (1 / (a * b) + 1 / (b * c) + 1 / (c * a))   :=  by sorry
