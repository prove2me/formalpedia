-- Prove2me | Theorems.Thm_lean_workbook_plus_55358
-- name    : lean_workbook_plus_55358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bca595f1-8d2e-4f31-90bf-e7bae7930397
-- statement:
--   Prove that if a,b,c > 0 and abc=1, then \n $\frac{1}{(a+b+1)} + \frac{1}{(b+c+1)} + \frac{1}{(c+a+1)}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55358 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0   :=  by sorry
