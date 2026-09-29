-- Prove2me | Theorems.Thm_lean_workbook_plus_38703
-- name    : lean_workbook_plus_38703
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7cf3fde4-da53-4761-a5b6-f5f3fc5332bf
-- statement:
--   If you want to see how many digits of n written in base k, n,k naturals, just think 'well I got d digits in base k, with d=1,2..., so what is the first number n written in base k with d digits and what is the last?', well, we add up the d-esim digit when n reaches $k^{d-1}$ and it keeps on d digits until $n=k^d-1$ , so if $k^{d-1}\leq n <k^d$ , then the number of digits is d. and so $d-1 \leq \log_k n <d$ , then, using the definition of the integer part (or floor function which in natural numbers is the same) you got $d=1+[\log_k n]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38703 (n k : ℕ) (hn : 1 < n) (hk : 1 < k) : ∃ d : ℕ, (k^(d-1) ≤ n ∧ n < k^d) ↔ d = 1 + Nat.floor (Real.logb k n)   :=  by sorry
