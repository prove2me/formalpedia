-- Prove2me | Theorems.Thm_lean_workbook_plus_70537
-- name    : lean_workbook_plus_70537
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/60e328f4-8c1a-4883-bb3c-cc720d298944
-- statement:
--   Let $a,b,c$ be integers such that. $\frac{ab}{c}+\frac{bc}{a}+\frac{ac}{b}$ is an integer. Prove that each of the number $\frac{ab}{c},\frac{bc}{a},\frac{ac}{b}$ is also an integer
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70537 (a b c : ℤ) (h : ∃ k : ℤ, k = ab / c + bc / a + ac / b) : ∃ k : ℤ, k = ab / c ∧ ∃ k : ℤ, k = bc / a ∧ ∃ k : ℤ, k = ac / b   :=  by sorry
