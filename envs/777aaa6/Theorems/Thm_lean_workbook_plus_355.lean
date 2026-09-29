-- Prove2me | Theorems.Thm_lean_workbook_plus_355
-- name    : lean_workbook_plus_355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/229d4006-db3e-44a2-997c-1177aba67086
-- statement:
--   Let $a,b,c>0$ . Show that $(a+b+c)\left( \frac{1}{a}+\frac{1}{b} + \frac{1}{c}\right) \geq 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_355 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9   :=  by sorry
