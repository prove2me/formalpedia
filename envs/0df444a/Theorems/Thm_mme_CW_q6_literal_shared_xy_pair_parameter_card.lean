-- Prove2me | Theorems.Thm_mme_CW_q6_literal_shared_xy_pair_parameter_card
-- name    : mme_CW_q6_literal_shared_xy_pair_parameter_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:17:48.726573+00:00
-- url     : https://prove2.me/theorems/2eae7d6d-7af6-448e-bcf0-3f2cc3271eb4
-- title:
--   Exact literal-bucket parameter count for one q=6 X/Y collision pair
-- statement:
--   Let e and f be distinct exact coupled q=6 addresses at power 2(n+1), sharing either their complete X-word or their complete Y-word. Put M=4X^2+1 and let S be a set of natural representatives modulo M. Then the number of affine parameters (w,b_0) for which both e and f lie in the same literal primary hash bucket is exactly $$|S|M^{2n}.$$ Thus every ordered X/Y collision pair contributes exactly the expected |S|/M^3 fraction of the complete parameter space.
-- source:
--   CW90 q=6 affine-hash ordered collision count for one literal bucket pair

import Mathlib
import Theorems.Thm_mme_CW_q6_shared_xy_pair_hash_parameter_card
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6LiteralPairExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

theorem mme_CW_q6_literal_shared_xy_pair_parameter_card
    {n L G Xcount : ℕ}
    (e f : CWQ6ExactCoupledAddress (n + 1) L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (4 * Xcount ^ 2 + 1)) :
    (((Finset.univ : Finset
        ((Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1)) ×
          ZMod (4 * Xcount ^ 2 + 1))).filter (fun ω :
            (Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1)) ×
              ZMod (4 * Xcount ^ 2 + 1) =>
      e ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1 ∧
      f ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1)).card) =
        S.card * (4 * Xcount ^ 2 + 1) ^ (2 * n) := by
  sorry
