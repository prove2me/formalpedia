-- Prove2me | Theorems.Thm_lean_workbook_plus_65500
-- name    : lean_workbook_plus_65500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d27190ed-f6b9-41d1-afab-be65e5c55a8a
-- statement:
--   Let $a, b,c> 0$ and $a+b+c+1=4abc$ . Prove that $$\frac{1}{2a+1}+\frac{1}{2b+1}+\frac{1}{2c+1}=1.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65500 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c + 1 = 4 * a * b * c) : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) = 1   :=  by sorry
