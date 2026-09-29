-- Prove2me | Theorems.Thm_lean_workbook_plus_15822
-- name    : lean_workbook_plus_15822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a8bb7208-251b-4e99-b9c2-b8691a0edade
-- statement:
--   Given that $a > 0$ and $b > 0$, prove that $(a + b)^2 \geq 4ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15822 (a b : ℝ) (hab : a > 0 ∧ b > 0) : (a + b) ^ 2 ≥ 4 * a * b   :=  by sorry
