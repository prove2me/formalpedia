-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_common_halving
-- name    : mme_CW_q6_primary_hash_sqrt_capacity_common_halving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:44:32.214012+00:00
-- url     : https://prove2.me/theorems/f8bb5271-c59e-487b-8abb-bb0b3fcc2547
-- title:
--   Primary q=6 hash capacity with one common balanced halving
-- statement:
--   Fix $\tau$ with $3\tau\ge2$, and put
--
--   $$\lambda=\frac{2}{6^{3\tau}+2},\qquad L=\lfloor\lambda N\rfloor,\qquad G=N-L$$
--
--   for the even lengths $N=2n$. There is a constant $C\ge0$ such that, for every sufficiently large $n$, one can choose a primary $q=6$ hash family with $A$ outer fibers and common inner size $H$ whose entries all admit one and the same balanced split of the $2N$ coupled positions. For
--
--   $$s=36^{2G}6^{2L},\qquad R=4\,6^{3\tau}(6^{3\tau}+2),$$
--
--   the retained family satisfies
--
--   $$R^{2N}e^{-C\sqrt{N+1}}\le A^3H^2(s^3)^\tau.$$
--
--   The family-wide common split balances the X word on the first source half and the Y word on the second source half for every retained entry. This is the compatibility needed to realize rows 121 and 211 on the literal paired source without independently reindexing addresses. The exponential rate is identical to the ordinary primary-hash capacity; only the subexponential constant changes.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Sections 5 and 6.3; the common-halving refinement is the source-faithful paired-row extraction obtained by double-counting balanced bipartitions and absorbing the polynomial thinning loss.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_common_paired_halving

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_CW_q6_primary_hash_sqrt_capacity_common_halving
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
              raw ^ (2 * N) *
                  Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
                (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                  ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  sorry
