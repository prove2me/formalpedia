-- Prove2me | Theorems.Thm_lean_workbook_plus_35693
-- name    : lean_workbook_plus_35693
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9bbeaf4a-4735-4f4c-8850-ea823ff06587
-- statement:
--   Let $f(x)=|x^2-\frac 12|$ , $\max_{x\in[-1,+1]}f(x)=\frac 12$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35693 ∀ x ∈ Set.Icc (-1 : ℝ) 1, abs (x^2-(1/2)) ≤ 1/2   :=  by sorry
