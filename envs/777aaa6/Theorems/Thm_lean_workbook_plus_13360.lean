-- Prove2me | Theorems.Thm_lean_workbook_plus_13360
-- name    : lean_workbook_plus_13360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/bd24c8b7-bda5-4b17-9caf-6416d155e2e2
-- statement:
--   Given the sequences ${x_n}$ and ${y_n}$ defined by $x_0=3,y_0=2, x_n = 3x_{n-1}+4y_{n-1}, y_n = 2x_{n-1}+3y_{n-1} \forall n$, prove that $(x_n, y_n)$ are roots of the Pell's equation: $x^2-2y^2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13360 (x y : ℕ → ℕ) (hx : x 0 = 3) (hy : y 0 = 2) (hn: ∀ n, x (n + 1) = 3 * x n + 4 * y n) (h'n: ∀ n, y (n + 1) = 2 * x n + 3 * y n) : ∀ n, (x n)^2 - 2 * (y n)^2 = 1   :=  by sorry
