-- Prove2me | Theorems.Thm_lean_workbook_plus_82300
-- name    : lean_workbook_plus_82300
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6a6f131c-e373-4ae9-bc18-bba27a4e7675
-- statement:
--   Consider $s_k = \sum_{j=1}^k a_j$ , for all $1\leq k \leq 100$ . If for some $k$ we have $100 \mid s_k$ , take $m=1$ , $n=k$ . If not, there will be two of them, say $s_p$ and $s_q$ , with $1\leq p < q \leq 100$ and $100 \mid s_q - s_p$ ; take $m=p+1$ , $n=q$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82300  (a : ℕ → ℤ)
  (h₀ : ∀ k, 1 ≤ k ∧ k ≤ 100 → 100 ∣ (∑ j in Finset.Icc 1 k, a j)) :
  ∃ m n, 1 ≤ m ∧ m < n ∧ n ≤ 100 ∧ 100 ∣ (∑ j in Finset.Icc m n, a j)   :=  by sorry
