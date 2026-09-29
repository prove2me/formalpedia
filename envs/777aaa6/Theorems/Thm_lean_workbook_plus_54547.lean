-- Prove2me | Theorems.Thm_lean_workbook_plus_54547
-- name    : lean_workbook_plus_54547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fc4c64dd-695d-4713-9145-fe74205efe25
-- statement:
--   Create a sequence $\{a_n\}_{n=0}^{+\infty}$ satisfying: $\begin{cases} a_0 = 2 \ a_n = 2a_{n-1} - 1\end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54547 : ∃ a : ℕ → ℤ, a 0 = 2 ∧ ∀ n, a (n + 1) = 2 * a n - 1   :=  by sorry
