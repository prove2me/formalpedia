-- Prove2me | Theorems.Thm_lean_workbook_plus_6159
-- name    : lean_workbook_plus_6159
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/506e3299-5ae6-4cad-8dda-9fc54e01942c
-- statement:
--   With x,y,z>0. Prove that: \n $\frac{1}{4a}+\frac{1}{4b}+\frac{1}{4c}\geq \frac{1}{2a+b+c}+\frac{1}{2b+c+a}+\frac{1}{2c+a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (4 * a) + 1 / (4 * b) + 1 / (4 * c) ≥ 1 / (2 * a + b + c) + 1 / (2 * b + c + a) + 1 / (2 * c + a + b)   :=  by sorry
