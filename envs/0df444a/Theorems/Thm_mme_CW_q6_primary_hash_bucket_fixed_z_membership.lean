-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
-- name    : mme_CW_q6_primary_hash_bucket_fixed_z_membership
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:03:58.285769+00:00
-- url     : https://prove2.me/theorems/77652458-a866-40de-9bf9-e8f6f6f9ed19
-- title:
--   Pointwise difference-equation characterization of the q=6 hash bucket
-- statement:
--   For an exact coupled q=6 address $e=(x,y,z)$, membership in the literal common-label affine hash bucket is equivalent to two conditions: the doubled X-minus-Z linear difference equation vanishes, and the doubled Z-hash is a retained label. Explicitly,\n\n$$\ne\in E_{b_0,w,S}\quad\Longleftrightarrow\quad\sum_j(2x_j-\operatorname{code}(z_j))w_j=0\ \text{ and }\ \exists s\in S,\ h_Z(b_0,w,z)=2s.\n$$\n\nThe q=6 support identity $h_X+h_Y=2h_Z$ makes the Y-hash condition automatic after the X and Z hashes agree. This theorem is the exact interface between fixed-Z linear-form moments and the concrete hash bucket, without any collision pruning or tensor claim.
-- source:
--   Doubled-hash arithmetic in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 270--271

import Mathlib
import Definitions.Def_mme_CW_q6_primary_hash_bucket
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open BigOperators MME

set_option autoImplicit false

theorem mme_CW_q6_primary_hash_bucket_fixed_z_membership
    (N L G Xcount : ℕ)
    (S : Finset ℕ)
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1))
    (e : CWQ6ExactCoupledAddress N L G) :
    e ∈ cwQ6PrimaryHashBucket N L G Xcount S b0 w ↔
      (∑ j,
        ((2 * ((e.1 0 j).val : ZMod (4 * Xcount ^ 2 + 1))) -
          (cwQ6CoupledZHashCode (e.1 2 j) :
            ZMod (4 * Xcount ^ 2 + 1))) * w j) = 0 ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash b0 w (e.1 2) =
          2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
  sorry
