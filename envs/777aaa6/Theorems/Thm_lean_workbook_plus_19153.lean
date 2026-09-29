-- Prove2me | Theorems.Thm_lean_workbook_plus_19153
-- name    : lean_workbook_plus_19153
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a843e876-4589-4fb9-9f01-df26f9898478
-- statement:
--   Prove that $C(n , k)=C(n, n-k)$, where $C(n,k)$ are numbers satisfying the following conditions: 1) $C(n,n)=C(n,0)=1$, 2) $C(n+1,k)=2^kC(n,k)+C(n , k-1)$ for $n \geq k \geq 1$, and $0 \leq k \leq n$, $k , n \in Z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19153 (n k : ℕ) (h₁ : n ≥ k) (h₂ : 0 < k) : choose n k = choose n (n - k)   :=  by sorry
