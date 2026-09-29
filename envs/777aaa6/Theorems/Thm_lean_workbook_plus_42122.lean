-- Prove2me | Theorems.Thm_lean_workbook_plus_42122
-- name    : lean_workbook_plus_42122
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/99e24204-dba9-489a-9cf3-db786dce8bdf
-- statement:
--   Given a sequence $(x_n)$ such that $x_0=x_1=1$ and $(n+3)x_{n+1}=(2n+3)x_n+3nx_{n-1} \forall n \in N$, prove that this is an integer sequence.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42122 (n : ℕ) (x : ℕ → ℕ) (h₀ : x 0 = 1) (h₁ : x 1 = 1) (h₂ : ∀ n, (n + 3) * x (n + 1) = (2 * n + 3) * x n + 3 * n * x (n - 1)) : ∀ n, ∃ k : ℤ, x n = k   :=  by sorry
