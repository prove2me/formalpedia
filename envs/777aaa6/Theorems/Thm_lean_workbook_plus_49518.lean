-- Prove2me | Theorems.Thm_lean_workbook_plus_49518
-- name    : lean_workbook_plus_49518
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3932a6dc-a560-4d66-a00a-75b8c9af6293
-- statement:
--   Prove that if $a, b, c > 1$, then $2b + 2c - 3bc - 1 > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49518 : ∀ a b c : ℝ, a > 1 ∧ b > 1 ∧ c > 1 → 2 * b + 2 * c - 3 * b * c - 1 > 0   :=  by sorry
