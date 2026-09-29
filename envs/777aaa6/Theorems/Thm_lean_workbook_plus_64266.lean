-- Prove2me | Theorems.Thm_lean_workbook_plus_64266
-- name    : lean_workbook_plus_64266
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1ce2cd6f-d6c2-4d1c-94bf-36d37d75dc4a
-- statement:
--   prove that for $a,b,c>0$, $\frac{3}{\frac{1}{a+1}+\frac{1}{b+1}+\frac{1}{c+1}}\geq 1+\frac{3}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64266 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 / (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1))) ≥ 1 + (3 / (1 / a + 1 / b + 1 / c))   :=  by sorry
