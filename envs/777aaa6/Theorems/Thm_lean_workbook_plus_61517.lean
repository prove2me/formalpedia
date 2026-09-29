-- Prove2me | Theorems.Thm_lean_workbook_plus_61517
-- name    : lean_workbook_plus_61517
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2a017eb8-60cc-4989-bda7-627bf74a4169
-- statement:
--   Let $ 2c\ge a\ge b\ge c> 0 $ . Prove that \n $$abc\ge(2a-b)(2b-c)(2c-a)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61517 (a b c : ℝ) (h₁ : 2 * c ≥ a ∧ a ≥ b ∧ b ≥ c) (h₂ : c > 0) : a * b * c ≥ (2 * a - b) * (2 * b - c) * (2 * c - a)   :=  by sorry
