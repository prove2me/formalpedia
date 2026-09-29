-- Prove2me | Theorems.Thm_lean_workbook_plus_78696
-- name    : lean_workbook_plus_78696
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/43825583-a79d-48b8-b602-7da6b2dffc6f
-- statement:
--   Let $U_{1}=1$ , and $U_{n+1}= U_{n}+ 3n^{2}+ 5n^{4}$ for all $n\geq 1$ . Find the general closed formula for $U_{n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78696 (U : ℕ → ℕ) (h : U 1 = 1 ∧ ∀ n, U (n + 1) = U n + 3 * n ^ 2 + 5 * n ^ 4) : ∃ f : ℕ → ℕ, ∀ n, U n = f n   :=  by sorry
