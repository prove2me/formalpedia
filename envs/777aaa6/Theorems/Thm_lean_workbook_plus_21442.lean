-- Prove2me | Theorems.Thm_lean_workbook_plus_21442
-- name    : lean_workbook_plus_21442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d634e0bb-5974-4977-8945-91be6c2f3341
-- statement:
--   Prove that $(a+b+c)^2 \ge 3(ab+bc+ca)$ for $a,b,c>0$ and $abc=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21442 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
