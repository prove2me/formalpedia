-- Prove2me | Theorems.Thm_lean_workbook_plus_23509
-- name    : lean_workbook_plus_23509
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1aab49b4-2854-4e61-905c-89335d2803df
-- statement:
--   Determine the general term of the sequence ( $a_n$ ) given by $a_0 =\alpha > 0$ and $a_{n+1} =\frac{a_n}{1+a_n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23509 (α : ℝ) (α_pos : 0 < α) : ∃ a : ℕ → ℝ, a 0 = α ∧ ∀ n, a (n + 1) = a n / (1 + a n)   :=  by sorry
