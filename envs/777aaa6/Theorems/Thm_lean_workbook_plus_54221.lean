-- Prove2me | Theorems.Thm_lean_workbook_plus_54221
-- name    : lean_workbook_plus_54221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6e4f5cf8-b483-4575-9e8d-5ddb47278da7
-- statement:
--   Let f be a function defined by $ f(n) = 2f(n - 1) + 3f(n - 2)$ , where $ f(1) = 1$ and $ f(2) = 2$ . Determine $ f(5)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54221 (f : ℕ → ℕ) (h₁ : f 1 = 1) (h₂ : f 2 = 2) (h₃ : ∀ n, f (n + 2) = 2 * f (n + 1) + 3 * f n) : f 5 = 61   :=  by sorry
