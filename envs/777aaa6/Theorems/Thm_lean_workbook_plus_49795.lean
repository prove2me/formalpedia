-- Prove2me | Theorems.Thm_lean_workbook_plus_49795
-- name    : lean_workbook_plus_49795
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/2fb0318a-0905-4d35-81b6-cd2179ff70cd
-- statement:
--   Prove $\lim \limits_{x \to 0}\frac{\sin(x)}{x} = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49795 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |sin x / x - 1| < ε   :=  by sorry
