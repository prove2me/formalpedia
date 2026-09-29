-- Prove2me | Theorems.Thm_lean_workbook_plus_79471
-- name    : lean_workbook_plus_79471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/18fd6f34-5c5f-424f-9d0c-8d3518c85fa5
-- statement:
--   A model can be built thusly. Consider the set $S = \{1,2,\ldots,n\}$ , and the set $A = \{ T\subset S \ ; \ |T| = n-k+1\}$ . Clearly $|A| = \binom {n} {n-k+1} = \binom {n} {k-1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79471  (n k : ℕ)
  (h₀ : 0 < k ∧ 0 < n)
  (h₁ : n ≥ k) :
  Nat.choose n (k - 1) = Nat.choose n (n - k + 1)   :=  by sorry
