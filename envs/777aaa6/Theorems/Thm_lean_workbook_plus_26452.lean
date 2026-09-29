-- Prove2me | Theorems.Thm_lean_workbook_plus_26452
-- name    : lean_workbook_plus_26452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/7a7a3f74-807c-4e52-bbe6-613f09316309
-- statement:
--   Let the series $ {x_n} $ be given by: $ x_1 = a $ where $ a > 0 $, $ x_{n+1} = \frac{(x_n)^2 + 2}{3}, n \geq 1 $. Show that if a is such that $ x_2 > x_1 $, then the series is strictly growing. And if a is such that $ x_2 < x_1 $, the series is strictly decreasing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26452 (a : ℝ) (x : ℕ → ℝ) (hx: x 1 = a) (hn: ∀ n:ℕ, x (n+1) = (x n)^2 + 2 / 3) : (x 2 > x 1 → ∀ n:ℕ, x (n+1) > x n) ∧ (x 2 < x 1 → ∀ n:ℕ, x (n+1) < x n)   :=  by sorry
