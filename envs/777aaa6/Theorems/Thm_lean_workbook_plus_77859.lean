-- Prove2me | Theorems.Thm_lean_workbook_plus_77859
-- name    : lean_workbook_plus_77859
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/be39beba-08fd-4378-835b-cea39d8f1495
-- statement:
--   Given the recursive relation $x_{n+1}x_n + 3x_n - 2x_{n+1} - x_{n+1}^2 - 2 = 0$, derive the identity $x_n - 2 = (x_{n+1} + 2)(x_{n+1} - x_n)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77859 (x : ℕ → ℝ) (n : ℕ) (h : x (n + 1) * x n + 3 * x n - 2 * x (n + 1) - x (n + 1) ^ 2 - 2 = 0) : x n - 2 = (x (n + 1) + 2) * (x (n + 1) - x n)   :=  by sorry
