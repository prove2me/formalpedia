-- Prove2me | Theorems.Thm_lean_workbook_plus_20621
-- name    : lean_workbook_plus_20621
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b72094f7-379b-484e-9546-7d105a3be4b2
-- statement:
--   Prove $\lim \limits_{x \to 0}\frac{e^x-1}{x} = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20621 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |(e^x - 1) / x - 1| < ε   :=  by sorry
