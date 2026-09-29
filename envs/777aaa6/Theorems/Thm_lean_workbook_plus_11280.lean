-- Prove2me | Theorems.Thm_lean_workbook_plus_11280
-- name    : lean_workbook_plus_11280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2e1108e9-4df2-4959-94f4-83e208dec056
-- statement:
--   Find the closed form for $a_n$, given $a_n = 0.25\cdot\left((\sqrt{2}+1)^{2n-1}-(\sqrt{2}-1)^{2n-1}+2\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11280 (a : ℕ → ℝ) (a_n : ∀ n, a n = 0.25 * ((Real.sqrt 2 + 1) ^ (2 * n - 1) - (Real.sqrt 2 - 1) ^ (2 * n - 1) + 2)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
