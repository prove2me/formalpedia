-- Prove2me | Theorems.Thm_lean_workbook_plus_1895
-- name    : lean_workbook_plus_1895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2c40e0a7-29b0-4710-8eff-26d1e9338c6a
-- statement:
--   Expanding and simplifying, we have that $a^2+2b \geq a^2+2a+1 \implies 2b \geq 2a+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1895  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a^2 + 2 * b ≥ a^2 + 2 * a + 1) :
  2 * b ≥ 2 * a + 1   :=  by sorry
