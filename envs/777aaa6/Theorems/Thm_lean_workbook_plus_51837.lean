-- Prove2me | Theorems.Thm_lean_workbook_plus_51837
-- name    : lean_workbook_plus_51837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e0f9f8a7-8b67-4cb9-a8c9-b6460c094f16
-- statement:
--   Prove that any real solution of $x^{3}+px+q=0$ satisfies the inequality $4xq\leq p^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51837 (x : ℝ) (p q : ℝ) (hx : x^3 + p * x + q = 0) : 4 * x * q ≤ p^2   :=  by sorry
