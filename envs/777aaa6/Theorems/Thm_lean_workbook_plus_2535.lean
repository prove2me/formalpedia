-- Prove2me | Theorems.Thm_lean_workbook_plus_2535
-- name    : lean_workbook_plus_2535
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c9dfc668-632f-4671-88d4-5b62d89f49ef
-- statement:
--   Prove the following identity.\n$\cos{2x} = 2\cos^2x - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2535 : ∀ x : ℝ, Real.cos (2 * x) = 2 * (Real.cos x)^2 - 1   :=  by sorry
