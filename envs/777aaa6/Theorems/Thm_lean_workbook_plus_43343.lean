-- Prove2me | Theorems.Thm_lean_workbook_plus_43343
-- name    : lean_workbook_plus_43343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2275d2f9-ed5a-425f-96d2-86de2743b547
-- statement:
--   Given positive reals a, b, c. Prove that: \n $ \frac{a}{1+a(1+b)}+\frac{b}{1+b(1+c)}+\frac{c}{1+c(1+a)} \leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43343 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (1 + a * (1 + b)) + b / (1 + b * (1 + c)) + c / (1 + c * (1 + a)) ≤ 1   :=  by sorry
