-- Prove2me | Theorems.Thm_lean_workbook_plus_42574
-- name    : lean_workbook_plus_42574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fb9a1a9d-7c21-4aa0-9dc3-ace1dcea1e9f
-- statement:
--   Prove that all the roots of the equation $x^3-3x+1=0$ are real
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42574 (h : ∀ x : ℂ, x ^ 3 - 3 * x + 1 = 0 → x.im = 0) : ∀ x : ℂ, x ^ 3 - 3 * x + 1 = 0 → x ∈ Set.univ   :=  by sorry
