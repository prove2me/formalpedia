-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded
-- name    : mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:57:56.965487+00:00
-- url     : https://prove2.me/theorems/19a0069b-9887-4302-8a82-bb3d17f016fc
-- title:
--   Primary q=6 capacity with one common balanced halving and a bounded fiber size
-- statement:
--   For every $\tau$ with $3\tau\geq2$, there is a nonnegative constant $C$ such that, for every sufficiently large even length $N=2n$, the optimized q=6 primary-hash construction has a uniform family with one coordinate halving shared by all retained entries.  Its common fiber size satisfies $H\leq4^N$, and
--
--   $$R^{2N}e^{-C\sqrt{N+1}}\leq A^3H^2\,S^{3\tau},$$
--
--   where $R=4\cdot6^{3\tau}(6^{3\tau}+2)$ and $S=36^{2G}6^{2L}$ at $L=\lfloor\lambda N\rfloor$, $G=N-L$.  The common-halving requirement costs only a polynomial factor, absorbed into the square-root exponential constant.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, primary hashing and the paired 121/211 square analysis.

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
import Theorems.Thm_mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
import Theorems.Thm_mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt

open MME BigOperators Filter Topology

set_option autoImplicit false

theorem mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        let N : ℕ := 2 * n
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N L G A H,
            ∃ _halving : family.CommonBalancedXYHalving,
              H ≤ 4 ^ N ∧
              raw ^ (2 * N) *
                  Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
                (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                  ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  sorry
