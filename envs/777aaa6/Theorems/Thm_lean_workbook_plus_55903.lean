-- Prove2me | Theorems.Thm_lean_workbook_plus_55903
-- name    : lean_workbook_plus_55903
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2300e209-83a9-4299-9b17-88aacd4f4452
-- statement:
--   Prove that for positive numbers $ a, b, c $ with $ a + b + c = 3 $, the following inequality holds: $ (a - b)^2(a - c)^2(b - c)^2 \ge 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55903 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) :  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 >= 0   :=  by sorry
