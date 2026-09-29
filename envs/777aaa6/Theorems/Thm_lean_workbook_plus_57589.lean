-- Prove2me | Theorems.Thm_lean_workbook_plus_57589
-- name    : lean_workbook_plus_57589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9e5b861b-de7c-4f21-abdb-9aba08d9968d
-- statement:
--   Prove that if a,b,c > 0 and abc=1, then \n $\frac{1}{(a+b+1)} + \frac{1}{(b+c+1)} + \frac{1}{(c+a+1)}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57589 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0   :=  by sorry
