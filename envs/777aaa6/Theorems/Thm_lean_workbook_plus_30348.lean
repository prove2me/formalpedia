-- Prove2me | Theorems.Thm_lean_workbook_plus_30348
-- name    : lean_workbook_plus_30348
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/41ea6b8e-ba46-485e-a6ef-d67602ef6b11
-- statement:
--   We have $ 4f(x) = (2x + p)^2 + r$ where $ r = 4q - p^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30348 (f : ℝ → ℝ) (p q r : ℝ) (h₁ : 4 * f x = (2 * x + p) ^ 2 + r) (h₂ : r = 4 * q - p ^ 2) : 4 * f x = (2 * x + p) ^ 2 + 4 * q - p ^ 2   :=  by sorry
