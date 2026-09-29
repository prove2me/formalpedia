-- Prove2me | Theorems.Thm_lean_workbook_plus_51965
-- name    : lean_workbook_plus_51965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/cd3769d7-506e-4dfe-8ae4-ba9c1e3cd47d
-- statement:
--   Let $\large\ a\geq b\geq c$ We have:\n$\large\ 1-c \geq 1-b \geq 1-a$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51965 (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) :
  1 - c ≥ 1 - b ∧ 1 - b ≥ 1 - a   :=  by sorry
