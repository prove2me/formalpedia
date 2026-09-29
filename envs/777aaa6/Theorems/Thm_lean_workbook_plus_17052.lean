-- Prove2me | Theorems.Thm_lean_workbook_plus_17052
-- name    : lean_workbook_plus_17052
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e8841d38-a694-4281-baa8-766f49955de7
-- statement:
--   Let $n$ be a positive integer. Define $A_n=( 1 \le a \le n; (a,n)=(a,n+1)= 1)$ . Prove that $\prod_{x\in A_n}x \equiv 1$ (mod n).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17052 (n : ℕ) (hn : 0 < n) (A_n : Finset { x : ℕ | 1 ≤ x ∧ x ≤ n ∧ (x, n) = 1 ∧ (x, n + 1) = 1}) : ∏ x in A_n, x ≡ 1 [ZMOD n]   :=  by sorry
