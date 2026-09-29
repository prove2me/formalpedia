-- Prove2me | Theorems.Thm_lean_workbook_plus_66119
-- name    : lean_workbook_plus_66119
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6d3d181b-e469-4913-bc4e-f9510be51c8f
-- statement:
--   Find a closed formula for $T(n)$ if $T(1) =1$ and for $n>1 : T(n) =\frac{1}{4-T(n-1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66119 (T : ℕ → ℝ) (h₁ : T 1 = 1) (h₂ : ∀ n, n > 1 → T n = 1 / (4 - T (n - 1))) : ∃ f : ℕ → ℝ, ∀ n, T n = f n   :=  by sorry
