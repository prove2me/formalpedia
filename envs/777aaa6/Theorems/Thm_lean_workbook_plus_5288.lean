-- Prove2me | Theorems.Thm_lean_workbook_plus_5288
-- name    : lean_workbook_plus_5288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/efceaa0f-1bee-4fef-b12b-53efde49fe11
-- statement:
--   Assume $a_k=k$ for all $1\leq k \leq n$ . Then since $\gcd(a_n, n+1) = \gcd(n,n+1)=1$ it means we must take $a_{n+1} = n+1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5288 {n : ℕ} (a : ℕ → ℕ) (h : ∀ k, 1 ≤ k ∧ k ≤ n → a k = k) : (∀ k, 1 ≤ k ∧ k ≤ n + 1 → a k = k) ↔ a (n + 1) = n + 1   :=  by sorry
