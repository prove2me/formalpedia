-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_many_z_stars
-- name    : mme_CW_q6_regular_primary_hash_bucket_many_z_stars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:25:32.545869+00:00
-- url     : https://prove2.me/theorems/0988ce72-947e-4a8f-9e61-ad70f04bc17d
-- title:
--   A regular q=6 profile has a literal bucket with many high-degree Z-stars
-- statement:
--   For a regular exact q=6 profile at power $2(n+1)$, write\n\n$$\nZ_0=\binom{2(n+1)}L\binom{2(n+1)-L}L,\qquad B=\binom{2G}G,\qquad M=4X^2+1.\n$$\n\nAssume $X>0$, $G>0$, and choose an integer threshold $H$ with $2MH\le B$. For every retained label set $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$, there are common affine hash parameters $(w,b_0)$ whose literal q=6 bucket satisfies\n\n$$\nB|S|Z_0\le 4M(2M+B)\,\bigl|\{z:H\le\deg_{E_{w,b_0}}(z)\}\bigr|.\n$$\n\nThis is the exact source-scale many-Z-star estimate inside the concrete bucket. It preserves the full shared-Z multiplicity; X/Y collision pruning and tensor realization are deliberately left to separate theorems.
-- source:
--   Regular-fiber dependent-weight averaging for q=6 in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 270--271

import Mathlib
import Theorems.Thm_mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Definitions.Def_mme_CW_q6_exact_address_incidence

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_regular_primary_hash_bucket_many_z_stars
    {n L G Xcount H : ℕ}
    (hX : 0 < Xcount) (hG : 0 < G)
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hH : 2 * (4 * Xcount ^ 2 + 1) * H ≤ Nat.choose (2 * G) G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2)) :
    ∃ w : Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1),
      ∃ b0 : ZMod (4 * Xcount ^ 2 + 1),
        Nat.choose (2 * G) G * S.card *
              (Nat.choose (2 * (n + 1)) L *
                Nat.choose (2 * (n + 1) - L) L) ≤
          4 * (4 * Xcount ^ 2 + 1) *
              (2 * (4 * Xcount ^ 2 + 1) + Nat.choose (2 * G) G) *
            ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
              H ≤ ((cwQ6PrimaryHashBucket
                (n + 1) L G Xcount S b0 w).filter
                  (fun e => e.1 2 = z)).card)).card := by
  sorry
