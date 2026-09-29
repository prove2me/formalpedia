-- Prove2me | Theorems.Thm_lean_workbook_plus_74791
-- name    : lean_workbook_plus_74791
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bbea9aa8-0511-447f-8da3-33f6a31a7f20
-- statement:
--   Prove the limit $\lim_{t \to 0} \frac{\exp t - 1}{t} = 1$ using the power series expansion of $e^t$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74791 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → |(exp t - 1) / t - 1| < ε   :=  by sorry
