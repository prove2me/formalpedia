-- Prove2me | Theorems.Thm_lean_workbook_plus_28374
-- name    : lean_workbook_plus_28374
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/07a7c324-4cd4-47c6-bb44-03d2c98b6713
-- statement:
--   Let the sequence $x_{2n}=-\frac 1n$ and $x_{2n+1}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28374 : ∃ x : ℕ → ℝ, ∀ n, (x (2 * n) = -1 / n ∧ x (2 * n + 1) = 1)   :=  by sorry
