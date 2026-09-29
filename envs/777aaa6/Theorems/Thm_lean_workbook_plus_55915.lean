-- Prove2me | Theorems.Thm_lean_workbook_plus_55915
-- name    : lean_workbook_plus_55915
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/07f7c531-b937-42b9-b98f-92732805a4dc
-- statement:
--   Prove that $\\lim_{y\\to0} \\frac{\\sin(y)}{y} = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55915 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ y : ℝ, y ∈ Set.Ioo (-δ) δ → |sin y / y - 1| < ε   :=  by sorry
