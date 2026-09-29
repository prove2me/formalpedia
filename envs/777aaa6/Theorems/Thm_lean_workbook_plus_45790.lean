-- Prove2me | Theorems.Thm_lean_workbook_plus_45790
-- name    : lean_workbook_plus_45790
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/587239ac-8467-48ac-b828-f713f65fbfc1
-- statement:
--   Prove that \\( \lim_{x\to1} \frac {\ln x}{x - 1} = 1 \\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45790 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo 1 δ → |(Real.log x) / (x - 1) - 1| < ε   :=  by sorry
