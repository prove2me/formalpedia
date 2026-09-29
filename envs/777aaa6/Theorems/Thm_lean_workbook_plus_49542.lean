-- Prove2me | Theorems.Thm_lean_workbook_plus_49542
-- name    : lean_workbook_plus_49542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/113f0e0e-a1b4-4683-9b1b-12ecdb1d0f42
-- statement:
--   Prove the following statements directly using the formal \\(\\varepsilon \\),\\(\\delta \\) definition.ii) \\(\\underset{x\\to 1}{\\mathop{\\lim }}\\,\\frac{x+3}{{{x}^{2}}+x+4}=\frac{2}{3}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49542 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo 1 δ → |(x + 3) / (x^2 + x + 4) - 2 / 3| < ε   :=  by sorry
