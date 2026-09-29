-- Prove2me | Theorems.Thm_lean_workbook_plus_70193
-- name    : lean_workbook_plus_70193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1fcdcade-821c-4e5d-b086-d9d499979e61
-- statement:
--   Find the sequence $\{x_1, x_2, x_3, \ldots\}$ where $x_1=r$ and $x_k=2^{k-1} \cdot x_1$ for some real number $r$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70193 (r : ℝ) (n : ℕ) : ∃ f : ℕ → ℝ, f 1 = r ∧ ∀ k, f k = (2 : ℝ)^(k-1) * f 1   :=  by sorry
