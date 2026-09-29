-- Prove2me | Theorems.Thm_lean_workbook_plus_24692
-- name    : lean_workbook_plus_24692
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4076bbaa-ecf5-421a-a24c-16403246b4fa
-- statement:
--   Proof that for all positive integer $n$ , $1+\sum_{i=0}^{n}{F_{4i}} =(\sum_{i=0}^{n}{\binom{2n-i}{i}})^2$ \nNote that $F_0=0,F_1=1$ and $F_{t+2}=F_{t+1}+F_t$ for all $t \in \mathbb{Z}^{+}_{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24692 : ∀ n : ℕ, 1 + ∑ i in Finset.range (n+1), fib 4*i = (∑ i in Finset.range (n+1), choose (2*n-i) i)^2   :=  by sorry
