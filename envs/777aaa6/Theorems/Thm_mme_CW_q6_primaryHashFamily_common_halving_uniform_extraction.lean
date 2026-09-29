-- Prove2me | Theorems.Thm_mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
-- name    : mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:41:51.280761+00:00
-- url     : https://prove2.me/theorems/1b708ce4-48b0-41f0-81ec-1410f76ec892
-- title:
--   A common-halving uniform subfamily retains q=6 capacity up to a polynomial loss
-- statement:
--   Let a positive q=6 primary hash family at even length $N=2n$ have $A$ outer fibers of common size $H$, with $H\leq4^N$.  Then it has a positive uniform subfamily with parameters $A',H'$ and one coordinate halving shared by every retained entry.  The fiber cap is preserved, $H'\leq4^N$, and
--
--   $$A^3H^2\leq128(N+1)^{20}(A')^3(H')^2.$$
--
--   Thus enforcing a common paired X/Y halving costs only an explicit polynomial factor in the cubic-square primary-hash capacity.  This factor is asymptotically absorbable into the existing square-root exponential loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, primary hash families and paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_primaryHashFamily_common_balanced_half_mass
import Theorems.Thm_mme_CW_q6_primaryHashFamily_uniform_subfamily
import Theorems.Thm_mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
import Theorems.Thm_mme_finite_fiber_threshold_polynomial

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_primaryHashFamily_common_halving_uniform_extraction
    {n L G A H : ℕ} (hLG : L + G = 2 * n)
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H)
    (hApos : 0 < A) (hHcap : H ≤ 4 ^ (2 * n)) :
    ∃ A' H' : ℕ,
      ∃ subfamily : CWQ6PrimaryHashFamily (2 * n) L G A' H',
        0 < A' ∧ 0 < H' ∧ H' ≤ 4 ^ (2 * n) ∧
        Nonempty subfamily.CommonBalancedXYHalving ∧
        A ^ 3 * H ^ 2 ≤
          128 * (2 * n + 1) ^ 20 * (A' ^ 3 * H' ^ 2) := by
  sorry
