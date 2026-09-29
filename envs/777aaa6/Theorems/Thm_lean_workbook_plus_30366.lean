-- Prove2me | Theorems.Thm_lean_workbook_plus_30366
-- name    : lean_workbook_plus_30366
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/17ba646d-6f15-4bbe-8e89-db49e23ba1f4
-- statement:
--   Prove that $\lim_{x \to 0}\frac{x}{\sin(x)}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30366 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |x / Real.sin x - 1| < ε   :=  by sorry
