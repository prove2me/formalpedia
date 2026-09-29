-- Prove2me | Theorems.Thm_lean_workbook_plus_62516
-- name    : lean_workbook_plus_62516
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a807e765-d28d-4c14-aa70-e3d5b6be3434
-- statement:
--   Given the quadratic trinomial $ f (x) = x ^ 2 + ax + b $ with integer coefficients, satisfying the inequality $ f (x) \geq - {9 \over 10} $ for any $ x $ . Prove that $ f (x) \geq - {1 \over 4} $ for any $ x $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62516 (a b : ℤ) (f : ℤ → ℤ) (hf: f x = x^2 + a*x + b) : (∀ x : ℤ, f x ≥ -9/10) → ∀ x : ℤ, f x ≥ -1/4   :=  by sorry
