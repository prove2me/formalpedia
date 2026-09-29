-- Prove2me | Theorems.Thm_lean_workbook_plus_56537
-- name    : lean_workbook_plus_56537
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/531441e3-0d63-4f07-9665-013076d495eb
-- statement:
--   For $a,b>0,\frac{1}{a}+\frac{1}{b}=1,$ prove that $\frac{1}{a^2+4}+\frac{1}{b^2+4}\ge\frac{1}{2} .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56537 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : 1 / (a ^ 2 + 4) + 1 / (b ^ 2 + 4) ≥ 1 / 2   :=  by sorry
