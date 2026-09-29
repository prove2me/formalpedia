-- Prove2me | Theorems.Thm_lean_workbook_plus_6789
-- name    : lean_workbook_plus_6789
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/dd7fc873-8140-4348-99b2-4b8502cd59e0
-- statement:
--   prove or disprove $a^3+b^3+c^3\geq{a^2+b^2+c^2}$ given $a,b,c>0$ and $abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6789 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
