-- Prove2me | Theorems.Thm_lean_workbook_plus_16558
-- name    : lean_workbook_plus_16558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2b06d1cd-d1a3-4079-8702-03c0ff068fd9
-- statement:
--   If two linear expressions are equal for all values of $x$ , then their constants must be equal and the coefficients of the linear terms must be equal. In other words, if A, B, C, D are constants and $$Ax + B = Cx + D$$ for all $x$ , then we must have $A = C$ and $B = D$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16558  (a b c d : ℝ)
  (h₀ : ∀ x, a * x + b = c * x + d) :
  a = c ∧ b = d   :=  by sorry
