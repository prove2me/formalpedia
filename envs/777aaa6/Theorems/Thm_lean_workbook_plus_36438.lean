-- Prove2me | Theorems.Thm_lean_workbook_plus_36438
-- name    : lean_workbook_plus_36438
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5ac48ef0-d253-43d5-b61b-b8838217b86a
-- statement:
--   Prove that if $x + \epsilon_1 < a$, then $x < a$, given $\epsilon_1, \epsilon_2 > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36438 (x a : ℝ) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : x + ε₁ < a) : x < a   :=  by sorry
