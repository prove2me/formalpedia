-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars
-- name    : mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:16:18.916686+00:00
-- url     : https://prove2.me/theorems/637f9d5a-b967-4678-b3a4-56affbda60a6
-- title:
--   Same-parameter q=6 hashing and X/Y pruning retain many large shared Z-fibers
-- statement:
--   For the regular exact q=6 profile, put X=choose(n+1,G), B=choose(2G,G), M=4X²+1, and let Z be the exact Z-word family. Fix thresholds H≤K, a positive lower-tail gap R, a target Q, and S⊆{0,…,M−1}. Assume MK+R≤B and the explicit finite arithmetic budget displayed in the formal statement, which balances the arbitrary-gap Z-star incidence against the exact ordered X/Y collision moment. Then one literal affine bucket contains an X/Y-isolated subfamily I for which at least Q exact Z-fibers have cardinality at least H. Isolation is relative to the whole original bucket, and shared Z multiplicity is retained; the theorem makes no tensor-realization claim.
-- source:
--   CW90 q=6 affine hashing: same-parameter arbitrary-gap star incidence, ordered X/Y collision moment, and shared-Z-preserving pruning

import Mathlib
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Theorems.Thm_mme_finite_weighted_collision_budget_retains_fibers
import Theorems.Thm_mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars
    {n L G K H R Q : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (hHK : H ≤ K) (hR : 0 < R)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1))
    (hgap :
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1) * K + R ≤
        Nat.choose (2 * G) G)
    (harith :
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 3) *
            ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 *
            (2 *
                ((cwQ6ExactZWords (n + 1) L G).card *
                  Nat.choose (2 * G) G) *
              (Nat.choose (n + 1) G) ^ 2 * S.card *
              (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n)) +
          (K - H + 1) *
            (2 * Nat.choose (2 * G) G *
              (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 3) *
              S.card * (cwQ6ExactZWords (n + 1) L G).card) ≤
        (K - H + 1) *
          (R ^ 2 *
            (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 2) *
            S.card * (cwQ6ExactZWords (n + 1) L G).card)) :
    ∃ w : Fin (2 * n + 2) →
          ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
      ∃ b0 : ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
        ∃ I : Finset (CWQ6ExactCoupledAddress (n + 1) L G),
          I ⊆ cwQ6PrimaryHashBucket (n + 1) L G
              (Nat.choose (n + 1) G) S b0 w ∧
          (∀ e ∈ I,
            ∀ e' ∈ cwQ6PrimaryHashBucket (n + 1) L G
                (Nat.choose (n + 1) G) S b0 w,
              (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
          Q ≤ ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
            H ≤ (I.filter (fun e => e.1 2 = z)).card)).card := by
  sorry
