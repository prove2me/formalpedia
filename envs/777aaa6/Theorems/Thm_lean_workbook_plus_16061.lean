-- Prove2me | Theorems.Thm_lean_workbook_plus_16061
-- name    : lean_workbook_plus_16061
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/20ef8886-4c58-4037-a504-2aad6f28399b
-- statement:
--   Solve for $x$ in the inequality $-3 < 2x - 5 < 7$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16061 (x : ℝ) : -3 < 2*x - 5 ∧ 2*x - 5 < 7 ↔ 1 < x ∧ x < 6   :=  by sorry
