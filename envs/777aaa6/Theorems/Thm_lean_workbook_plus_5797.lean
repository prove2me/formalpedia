-- Prove2me | Theorems.Thm_lean_workbook_plus_5797
-- name    : lean_workbook_plus_5797
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ee0d0728-2ca9-4984-8e61-a254a1b4c847
-- statement:
--   Prove the limit $\lim_{x \rightarrow 0} \frac{x}{e^x - 1} = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5797 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |x / (Real.exp x - 1) - 1| < ε   :=  by sorry
