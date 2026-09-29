-- Prove2me | Theorems.Thm_lean_workbook_plus_20678
-- name    : lean_workbook_plus_20678
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fcb82dec-75bb-49b1-a72f-06b986e4a634
-- statement:
--   $1-\cos x\sim \frac{1}{2}x^2\ (x\to 0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20678 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |(1 - Real.cos x) - x^2 / 2| < ε * |x|   :=  by sorry
