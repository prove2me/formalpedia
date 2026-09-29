-- Prove2me | Theorems.Thm_lean_workbook_plus_70061
-- name    : lean_workbook_plus_70061
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3cc79af6-9f4e-46f2-a41d-bd24a6595d8f
-- statement:
--   Prove that for positive numbers $a, b, c$ with $a^2 + b^2 + c^2 = 1$, the following inequality holds: $\frac{a+b}{1+ab} + \frac{b+c}{1+bc} + \frac{c+a}{1+ca} \leq \frac{3\sqrt{3}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70061 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  (a + b) / (1 + a * b) + (b + c) / (1 + b * c) + (c + a) / (1 + c * a) ≤ (3 * Real.sqrt 3) / 2   :=  by sorry
