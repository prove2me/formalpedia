-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars
-- name    : mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:39:09.324017+00:00
-- url     : https://prove2.me/theorems/fa4bee93-4796-4447-8eff-acb803be2c52
-- title:
--   Transparent q=6 margins retain many shared Z-stars after X/Y pruning
-- statement:
--   For the exact regular q=6 profile, write X=choose(n+1,G), B=choose(2G,G), M=4X²+1, and let Z be the exact Z-word family. Given H≤K, R>0, S⊆range M and MK+R≤B, suppose the three explicit margins 16BM≤R², 5B≤8M(K−H+1), and 16MQ≤|S||Z| hold. Then some literal affine bucket has an X/Y-isolated subfamily I for which at least Q exact Z-fibers have cardinality at least H. Isolation is relative to the whole bucket, and shared Z multiplicity is retained.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–272: affine hashing, fixed-Z concentration, and X/Y collision deletion; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_CW_q6_collision_margin_arithmetic
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars
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
    (hRmargin :
      16 * Nat.choose (2 * G) G *
          (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤ R ^ 2)
    (hDmargin :
      5 * Nat.choose (2 * G) G ≤
        8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) *
          (K - H + 1))
    (hQmargin :
      16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) * Q ≤
        S.card * (cwQ6ExactZWords (n + 1) L G).card) :
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
