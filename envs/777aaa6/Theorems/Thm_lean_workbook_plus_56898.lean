-- Prove2me | Theorems.Thm_lean_workbook_plus_56898
-- name    : lean_workbook_plus_56898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ec041e77-6e20-4a4a-8e5c-3f35113901c6
-- statement:
--   Prove that $a-c \geq b-c \geq 0$ given $a \geq b \geq c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56898 (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) : a - c ≥ b - c ∧ b - c ≥ 0   :=  by sorry
