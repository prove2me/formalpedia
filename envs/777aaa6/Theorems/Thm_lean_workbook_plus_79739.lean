-- Prove2me | Theorems.Thm_lean_workbook_plus_79739
-- name    : lean_workbook_plus_79739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9a7b0ec3-b564-4adc-9e26-7459701aa2bd
-- statement:
--   For any positive a,b,c, prove that $\frac{1}{2+3a}+\frac{1}{2+3b}+\frac{1}{2+3c}\geq\frac{3}{2+a+b+c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (2 + 3 * a) + 1 / (2 + 3 * b) + 1 / (2 + 3 * c) ≥ 3 / (2 + a + b + c)   :=  by sorry
