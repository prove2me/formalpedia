-- Prove2me | Theorems.Thm_lean_workbook_plus_19096
-- name    : lean_workbook_plus_19096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/06601c00-e3f7-469a-b762-a889937d0df7
-- statement:
--   prove that: \n${ \frac{1}{a}+\frac{2}{a+b}+\frac{3}{a+b+c}<4(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}})$\nGiven: $ a,b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19096 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 2 / (a + b) + 3 / (a + b + c)) < 4 * (1 / a + 1 / b + 1 / c)   :=  by sorry
