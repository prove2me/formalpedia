-- Prove2me | Theorems.Thm_mme_three_directional_outer_joint_log_capacity
-- name    : mme_three_directional_outer_joint_log_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:37:54.873419+00:00
-- url     : https://prove2.me/theorems/9ff49257-cad5-4bad-aaa2-2dda8f0f1348
-- title:
--   Combine outer and joint logarithmic rates before the three-directional minimum
-- statement:
--   Let $A_i,H_i>0$, for $i\in\{0,1,2\}$, and define
--   $
--   P=(A_0A_1A_2)\min(H_1H_2,H_0H_2,H_0H_1).
--   $
--   Then
--   $
--   \log P=\min_{k\in\{0,1,2\}}
--   \left(\log A_k+\sum_{j\ne k}\log(A_jH_j)\right).
--   $
--   Moreover, if real arrays $a_i,r_i$ satisfy $a_i\le\log A_i$ and $r_i\le\log(A_iH_i)$, then
--   $
--   \min_k\left(a_k+\sum_{j\ne k}r_j\right)\le\log P.
--   $
--   The parameters may differ between orientations. This scalar composition keeps the minimum after the directional contributions are combined and needs no separate lower bound on $\log H_i$. It does not construct a matching or assert that the ideal capacity $P$ is attained.
-- source:
--   Elementary positive-real logarithm and minimum algebra, formalized using the pinned Mathlib Real.log_mul, Real.log_le_log, min_add_add_left, and min_le_min interfaces. Real.log_mul and Real.log_le_log are in Mathlib/Analysis/SpecialFunctions/Log/Basic.lean at revision777aaa61dcd2a1258d2b4962dbe983ede4d23b2e. This is a new formal scalar adapter for the product of three differently oriented retained star families and the unequal-alphabet induced-matching capacity. It does not assume or prove the tensor-product extraction, matching existence, or a global asymptotic value theorem.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

theorem mme_three_directional_outer_joint_log_capacity (A H : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hH : ∀ i, 0 < H i) :
    Real.log ((A 0 * A 1 * A 2) *
        min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1))) =
      min (Real.log (A 0) + Real.log (A 1 * H 1) + Real.log (A 2 * H 2))
        (min (Real.log (A 1) + Real.log (A 0 * H 0) + Real.log (A 2 * H 2))
          (Real.log (A 2) + Real.log (A 0 * H 0) + Real.log (A 1 * H 1))) ∧
    ∀ (a r : Fin 3 → ℝ),
      (∀ i, a i ≤ Real.log (A i)) →
      (∀ i, r i ≤ Real.log (A i * H i)) →
        min (a 0 + r 1 + r 2)
          (min (a 1 + r 0 + r 2) (a 2 + r 0 + r 1)) ≤
        Real.log ((A 0 * A 1 * A 2) *
          min (H 1 * H 2) (min (H 0 * H 2) (H 0 * H 1))) := by sorry
