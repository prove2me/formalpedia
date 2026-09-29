-- Prove2me | Theorems.Thm_lean_workbook_plus_22280
-- name    : lean_workbook_plus_22280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a7de4d2e-8ff7-4269-a1c5-92cf433e3842
-- statement:
--   First, we bound $n$ . Note that for $n\geq3$ , $n^k < n^k+n^m < n^{k+1}$ for $m\leq k$ . Thus, $n\leq 2$ . Furthermore, letting $n=1$ gives $1^a+1^b=1^c\to1+1=1$ , a contradiction. Thus, $n=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22280  (n k m a b c : ℕ)
  (h₀ : 0 < n ∧ 0 < k ∧ 0 < m ∧ 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : n^k + n^m = n^a + n^b + n^c)
  (h₂ : k ≤ a ∧ m ≤ b ∧ c ≤ k)
  (h₃ : n ≤ 2) :
  n = 2   :=  by sorry
