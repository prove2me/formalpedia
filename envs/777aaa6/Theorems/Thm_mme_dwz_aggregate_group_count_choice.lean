-- Prove2me | Theorems.Thm_mme_dwz_aggregate_group_count_choice
-- name    : mme_dwz_aggregate_group_count_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:27:09.457795+00:00
-- url     : https://prove2.me/theorems/e6c4b5cd-7d51-4b6a-a4b4-8f6b04a56b27
-- title:
--   DWZ aggregate mass supports the required rounded group count
-- statement:
--   Let $t$ be a positive integer and suppose an available aggregate mass is at least $A\ge 16t$. Then one can choose an integer number $q$ of groups such that
--
--   $$
--   q\ge \frac{A}{16t}
--   \qquad\text{and}\qquad
--   q(t+1)\le \mathrm{total}.
--   $$
--
--   The extra unit in each group's budget absorbs rounding in the greedy partition, while the same factor $16t$ appearing in the published square-bound denominator is preserved.
-- source:
--   Quantitative rounding step for Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Corollary 5.11 and the square analysis.

import Mathlib

set_option autoImplicit false

theorem mme_dwz_aggregate_group_count_choice
    (t : ℕ) (ht : 0 < t) (A total : ℝ)
    (hlarge : 16 * (t : ℝ) ≤ A) (hAtotal : A ≤ total) :
    ∃ q : ℕ,
      A / (16 * (t : ℝ)) ≤ (q : ℝ) ∧
      (q : ℝ) * ((t : ℝ) + 1) ≤ total := by
  sorry
