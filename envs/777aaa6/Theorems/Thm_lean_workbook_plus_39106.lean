-- Prove2me | Theorems.Thm_lean_workbook_plus_39106
-- name    : lean_workbook_plus_39106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2e8b034b-adcf-46ab-9646-f49a1b38fd4b
-- statement:
--   Given for some real $a, b, c, d$ ,\n$$P(x) = ax^4 + bx^3 + cx^2 + dx$$\n$$P(-5) = P(-2) = P(2) = P(5) = 1$$\nFind $P(10)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39106 (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x) : P (-5) = 1 ∧ P (-2) = 1 ∧ P 2 = 1 ∧ P 5 = 1 → P 10 = -71   :=  by sorry
