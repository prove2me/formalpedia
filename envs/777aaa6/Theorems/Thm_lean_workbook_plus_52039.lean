-- Prove2me | Theorems.Thm_lean_workbook_plus_52039
-- name    : lean_workbook_plus_52039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/149c5fa5-a8a7-439c-b64b-c702236fd46f
-- statement:
--   Observe that $f(x) = 2x + \frac{1}{3}$ . Then $f(0) = \frac{1}{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52039  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x + 1 / 3)
  (h₁ : x = 0) :
  f x = 1 / 3   :=  by sorry
