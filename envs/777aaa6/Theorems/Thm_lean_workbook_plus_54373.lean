-- Prove2me | Theorems.Thm_lean_workbook_plus_54373
-- name    : lean_workbook_plus_54373
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/53b399a7-fe77-4aec-b29d-f9f98115c2e2
-- statement:
--   Given $a, b, c$ are real numbers such that $a + b + c \geq abc$. Prove that $a^2 + b^2 + c^2 \geq abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54373 (a b c : ℝ) (h : a + b + c ≥ a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b * c   :=  by sorry
