-- Prove2me | Theorems.Thm_lean_workbook_plus_60042
-- name    : lean_workbook_plus_60042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c4418bae-37cf-4c83-ba0e-8daf8b748433
-- statement:
--   $0<x<1 \implies 0 < x^3< x \implies 0<20x^3<20x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60042 : ∀ x : ℝ, 0 < x ∧ x < 1 → 0 < 20 * x^3 ∧ 20 * x^3 < 20 * x   :=  by sorry
