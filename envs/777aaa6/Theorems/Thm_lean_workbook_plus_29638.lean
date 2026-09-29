-- Prove2me | Theorems.Thm_lean_workbook_plus_29638
-- name    : lean_workbook_plus_29638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/da229877-d2a6-498b-8ec8-a7d876157097
-- statement:
--   Prove that $4t^2+8t-5\le 0$ for $0\le t\le\frac{1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29638 : ∀ t : ℝ, t ∈ Set.Icc 0 (1 / 2) → 4 * t ^ 2 + 8 * t - 5 ≤ 0   :=  by sorry
