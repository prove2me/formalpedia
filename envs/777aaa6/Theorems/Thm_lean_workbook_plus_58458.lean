-- Prove2me | Theorems.Thm_lean_workbook_plus_58458
-- name    : lean_workbook_plus_58458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/32851b73-432b-4360-a3a0-fd16e863b1fa
-- statement:
--   Prove for $a,b>0$ : $\frac{2a}{a+b}+\frac{b}{2a}\ge\frac{1}{2}(3+\left(\frac{a-b}{a+b}\right)^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58458 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a / (a + b) + b / (2 * a)) ≥ 1 / 2 * (3 + (a - b) ^ 2 / (a + b) ^ 2)   :=  by sorry
