-- Prove2me | Theorems.Thm_lean_workbook_plus_66024
-- name    : lean_workbook_plus_66024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e9c8725c-0420-4eed-a8c6-2211f64bec8a
-- statement:
--   Therefore the condition is equivalent to $ {b\over b-1}\leq x\leq {a\over a-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66024  (x a b : ℝ)
  (h₀ : 1 < a ∧ 1 < b)
  (h₁ : b / (b - 1) ≤ x ∧ x ≤ a / (a - 1))
  (h₂ : 0 < a ∧ 0 < b)
  (h₃ : b ≤ a)
  : (b / (b - 1) ≤ x ∧ x ≤ a / (a - 1)) ↔ b / (b - 1) ≤ x ∧ x ≤ a / (a - 1)   :=  by sorry
