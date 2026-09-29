-- Prove2me | Theorems.Thm_lean_workbook_plus_11985
-- name    : lean_workbook_plus_11985
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/74beb01c-d8a4-43c7-b2c4-b71810d40ff7
-- statement:
--   Prove the inequality $63x^3 - 123 x^2 +61x -9 \le 0$ for all $x$ with $0 \le x \le 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11985 ∀ x: ℝ, 0 ≤ x ∧ x ≤ 1 → 63 * x ^ 3 - 123 * x ^ 2 + 61 * x - 9 ≤ 0   :=  by sorry
