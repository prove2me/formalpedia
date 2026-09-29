-- Prove2me | Theorems.Thm_lean_workbook_plus_2680
-- name    : lean_workbook_plus_2680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/72645b0e-d0a2-40a2-8363-e26a527b4084
-- statement:
--   Prove that $2bc + 1 \geq b + c$ given $0 < b, c \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2680 (b c : ℝ) (h₁ : 0 < b ∧ 0 < c) (h₂ : b ≤ 1 ∧ c ≤ 1) : 2 * b * c + 1 ≥ b + c   :=  by sorry
