-- Prove2me | Theorems.Thm_lean_workbook_plus_56059
-- name    : lean_workbook_plus_56059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/b1961fce-b54c-4a76-b0b8-d46bf3bc1841
-- statement:
--   Firstly, we have the inequality: $\frac{x}{{x + 1}} \ge \frac{x}{{\sqrt {{x^4} + 3} }} \Leftrightarrow {x^4} + 3 \ge {(x + 1)^2} \Leftrightarrow {(x - 1)^2}({x^2} + 2x + 2) \ge 0$ ( which is obvious )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56059  (x : NNReal) :
  x / (x + 1) ≥ x / (Real.sqrt (x^4 + 3))   :=  by sorry
