-- Prove2me | Theorems.Thm_lean_workbook_plus_73031
-- name    : lean_workbook_plus_73031
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4bf0eff6-2a7a-4dca-8893-e21e209f21d7
-- statement:
--   Find the constant $c$ in $I(\alpha)=\pi\ln\left(\sqrt{1-\alpha^2}+1\right)+c$ such that $I(0) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73031 (α : ℝ) (I : ℝ → ℝ) (h₁ : I = fun (α : ℝ) => π * Real.log (Real.sqrt (1 - α ^ 2) + 1) + c) (h₂ : I 0 = 0) : c = -π * Real.log 2   :=  by sorry
