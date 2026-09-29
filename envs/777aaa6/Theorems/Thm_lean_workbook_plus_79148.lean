-- Prove2me | Theorems.Thm_lean_workbook_plus_79148
-- name    : lean_workbook_plus_79148
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e2960ada-524e-4ee0-8cfc-21309b7b3997
-- statement:
--   Quadratic polynomials $P(x)$ and $Q(x)$ have leading coefficients of $2$ and $-2$ , respectively. The graphs of both polynomials pass through the two points $(16,54)$ and $(20,53)$ . Find ${P(0) + Q(0)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79148 (P Q : ℝ → ℝ) (hP : P = fun x => 2 * x ^ 2 + b * x + c) (hQ : Q = fun x => -2 * x ^ 2 + d * x + e) (hPQ : P 16 = 54 ∧ P 20 = 53) (hPQ : Q 16 = 54 ∧ Q 20 = 53) : P 0 + Q 0 = 116   :=  by sorry
