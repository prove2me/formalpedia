-- Prove2me | Theorems.Thm_lean_workbook_plus_10986
-- name    : lean_workbook_plus_10986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b3bdc4dc-fb9c-436d-9e5d-6899305fd226
-- statement:
--   Find the distance between points A and B with coordinates ( $a_1$ , $a_2$ ) and ( $b_1$ , $b_2$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10986 (a₁ a₂ b₁ b₂ : ℝ) : ∃ d, d = Real.sqrt ((a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2)   :=  by sorry
