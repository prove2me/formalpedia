-- Prove2me | Theorems.Thm_mme_nat_complete_group_floor_real_lower
-- name    : mme_nat_complete_group_floor_real_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:29:13.429493+00:00
-- url     : https://prove2.me/theorems/ff083173-97d2-46b0-aaef-7667f439be9a
-- title:
--   Discarding one incomplete repair group costs at most a factor two
-- statement:
--   Let $n$ objects be partitioned into complete groups of positive integer size $g$, and suppose a real lower bound $A\le n$ is already at least $2g$. Then the number $\lfloor n/g\rfloor$ of complete groups satisfies
--
--   $$
--   \frac{A}{2g}\le\left\lfloor\frac ng\right\rfloor.
--   $$
--
--   This is the exact integer-rounding estimate used when a retained family of broken tensor copies is partitioned into fixed-size Hole-Lemma repair groups; it accounts for the discarded incomplete final group by the explicit factor $2g$.
-- source:
--   Elementary Euclidean-division lemma used in the finite implementation of Duan--Wu--Zhou Corollary 5.11, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.3 and Equation (24), printed pp. 48--58.

import Mathlib.Tactic

set_option autoImplicit false

theorem mme_nat_complete_group_floor_real_lower
    (n g : ℕ) (A : ℝ)
    (hg : 0 < g)
    (hlarge : 2 * (g : ℝ) ≤ A)
    (hlower : A ≤ (n : ℝ)) :
    A / (2 * (g : ℝ)) ≤ ((n / g : ℕ) : ℝ) := by
  sorry
