-- Prove2me | Theorems.Thm_lean_workbook_plus_47604
-- name    : lean_workbook_plus_47604
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4a3e7c40-2ac2-4ad8-8262-52d3e85b51f5
-- statement:
--   Prove that $\lim_{x \to 1} \frac{x^3-1}{x-1}=3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47604 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo 1 δ → |(x^3 - 1) / (x - 1) - 3| < ε   :=  by sorry
