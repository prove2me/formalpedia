-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
-- name    : mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:32:21.005317+00:00
-- url     : https://prove2.me/theorems/586fa80f-450b-46e6-962c-aa85b7fae76d
-- title:
--   An eventually-large regular q=6 profile has a literal isolated bucket with many shared Z-stars
-- statement:
--   For a regular exact q=6 profile, write (X=\binom{n+1}{G}), (B=\binom{2G}{G}), (M=4X^2+1), and let (Z) be the exact Z-word family. If (G>0), (S\subseteq\{0,\ldots,M-1\}), and (400M\le B), then one literal affine bucket contains a subfamily isolated in X and Y relative to the whole bucket, with at least $$\left\lfloor\frac{|S||Z|}{16M}\right\rfloor$$ exact Z-fibers of cardinality at least $$\left\lfloor\frac{B}{8M}\right\rfloor.$$ The construction prunes only X/Y collisions, so shared Z multiplicity is retained.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–272: q=6 affine hashing and X/Y collision pruning; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_CW_q6_eventual_threshold_choice
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1))
    (hlarge :
      400 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤
        Nat.choose (2 * G) G) :
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
          (S.card * (cwQ6ExactZWords (n + 1) L G).card) /
                (16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤
            ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
              Nat.choose (2 * G) G /
                    (8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤
                (I.filter (fun e => e.1 2 = z)).card)).card := by
  sorry
