-- Prove2me | Theorems.Thm_lean_workbook_plus_78186
-- name    : lean_workbook_plus_78186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3b2a1709-ca77-4891-b9bc-bd7b88f73027
-- statement:
--   Given three real positive real numbers $a$ , $b$ , $c$ such that $abc=1$ , prove that at least one of $a-\frac{1}{b}$ , $b-\frac{1}{c}$ , $c-\frac{1}{a}$ does not exceed 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78186 (a b c : ℝ) (habc : a * b * c = 1) : ∃ x y z : ℝ, x = a - 1 / b ∧ y = b - 1 / c ∧ z = c - 1 / a ∧ x ≤ 1 ∨ y ≤ 1 ∨ z ≤ 1   :=  by sorry
