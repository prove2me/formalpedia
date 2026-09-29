-- Prove2me | Theorems.Thm_lean_workbook_plus_13067
-- name    : lean_workbook_plus_13067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e10ae13f-9f01-4896-b98a-4e7f501646e5
-- statement:
--   Prove the inequality using the AM-HM inequality: $\frac {1}{a + b}\leq \frac {1}{4a} + \frac {1}{4b}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13067 (a b : ℝ) (ha : a > 0) (hb : b > 0) : 1 / (a + b) ≤ 1 / (4 * a) + 1 / (4 * b)   :=  by sorry
