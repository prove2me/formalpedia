-- Prove2me | Theorems.Thm_lean_workbook_plus_34091
-- name    : lean_workbook_plus_34091
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/58e0a556-d4ce-463e-b806-40be0baf5cf1
-- statement:
--   Prove $\cos^3 x=\frac 34 \cos x+\frac 14 \cos 3x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34091 : ∀ x : ℝ, cos x ^ 3 = 3 / 4 * cos x + 1 / 4 * cos (3 * x)   :=  by sorry
