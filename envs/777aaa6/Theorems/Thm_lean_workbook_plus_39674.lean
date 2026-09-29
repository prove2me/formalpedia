-- Prove2me | Theorems.Thm_lean_workbook_plus_39674
-- name    : lean_workbook_plus_39674
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/54fff2fd-0305-4e62-a8ef-ffa82778fdd9
-- statement:
--   Prove that for $|x|\le\frac12,$ there is a positive constant $c$ such that $0<x-\ln(1+x)<cx^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39674 : ∃ c > 0, ∀ x : ℝ, |x| ≤ 1 / 2 → 0 < x - Real.log (1 + x) ∧ x - Real.log (1 + x) < c * x ^ 2   :=  by sorry
