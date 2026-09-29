-- Prove2me | Theorems.Thm_lean_workbook_plus_20175
-- name    : lean_workbook_plus_20175
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d330103a-4c72-4b0c-be8a-b888591eeafc
-- statement:
--   Prove that $\cos y = \sqrt{1 - x^2}$ for $y = \sin^{-1} x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20175 (x y : ℝ) (h₁ : 0 ≤ x ∧ x ≤ 1) (h₂ : y = arcsin x) : cos y = Real.sqrt (1 - x^2)   :=  by sorry
