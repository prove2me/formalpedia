-- Prove2me | Theorems.Thm_lean_workbook_plus_64007
-- name    : lean_workbook_plus_64007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/305e3f51-d1ce-4677-84fb-887b6f3275f8
-- statement:
--   For $\frac{1}{5}\leq{x_n}\leq{1}$ , $ \implies{x_{n+1}=\frac{1}{5}(x_{n}^3+\frac{1}{x_n})<\frac{1+5}{5}<2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64007 (x : ℝ) (hx: 1/5 ≤ x ∧ x ≤ 1) : 1/5 * (x^3 + 1/x) < 2   :=  by sorry
