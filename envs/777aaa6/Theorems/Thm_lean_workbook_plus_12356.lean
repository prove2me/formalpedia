-- Prove2me | Theorems.Thm_lean_workbook_plus_12356
-- name    : lean_workbook_plus_12356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c38a4c24-a648-48aa-ad5a-789045e7631b
-- statement:
--   Let $a,b>1 .$ Prove that \n $$\frac{a}{b-1}+\frac{b}{a-1}\geq \frac{2(a+b)}{a+b-2} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12356 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : a / (b - 1) + b / (a - 1) ≥ 2 * (a + b) / (a + b - 2)   :=  by sorry
