-- Prove2me | Theorems.Thm_lean_workbook_plus_81712
-- name    : lean_workbook_plus_81712
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/03649260-34bb-4b9c-9ebf-bcf2a27c0e71
-- statement:
--   Derive the limit: \\(\\lim_{{t \\to 0}} \\frac{{1 - \\cos t}}{{t^2}} = \\frac{1}{2}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81712 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → |(1 - Real.cos t) / t ^ 2 - 1 / 2| < ε   :=  by sorry
