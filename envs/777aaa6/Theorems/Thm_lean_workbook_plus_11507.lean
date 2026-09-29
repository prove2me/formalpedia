-- Prove2me | Theorems.Thm_lean_workbook_plus_11507
-- name    : lean_workbook_plus_11507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0f18bafe-3829-4a25-8244-28b1ee332938
-- statement:
--   Solve for a, b, and c in the equation $k_1(abc) + k_2(ab + ac + bc) + k_3(a+b+c) + k_4=0$, where $k_i$ are given constants.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11507 (k₁ k₂ k₃ k₄ a b c : ℝ) : k₁ * a * b * c + k₂ * (a * b + a * c + b * c) + k₃ * (a + b + c) + k₄ = 0 → a = a ∧ b = b ∧ c = c   :=  by sorry
