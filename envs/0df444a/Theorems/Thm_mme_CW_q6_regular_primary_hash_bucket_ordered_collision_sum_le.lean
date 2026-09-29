-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
-- name    : mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:30:05.832131+00:00
-- url     : https://prove2.me/theorems/73208eb0-2139-4669-bd1e-fc1e83ea0fe9
-- title:
--   Exact aggregate ordered X/Y collision bound for regular q=6 buckets
-- statement:
--   Let the exact coupled q=6 profile at N=n+1 be regular. Write $$Z=\binom{2N}{L}\binom{2N-L}{L},\quad B=\binom{2G}{G},\quad X=\binom NG,\quad M=4X^2+1.$$ For every retained label set S modulo M, let E_ω be the literal primary hash bucket at affine parameter ω=(w,b_0), and let C(E_ω) be the ordered set of distinct pairs in E_ω sharing X or Y. Then $$\sum_ω |C(E_ω)|\le 2ZBX^2|S|M^{2n}.$$ This is the source-scale first-hash collision moment: shared Z multiplicity is untouched, and only X/Y collisions are counted.
-- source:
--   CW90 q=6 affine-hash ordered X/Y collision expectation at journal pp. 270--271

import Mathlib
import Theorems.Thm_mme_CW_q6_literal_shared_xy_pair_parameter_card
import Theorems.Thm_mme_CW_q6_exact_subtype_collision_universe_card_le
import Theorems.Thm_mme_finite_incidence_first_second_moment_identities

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6CollisionSumExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

noncomputable local instance q6CollisionSumCoupledAddressFintype
    (N : ℕ) : Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

noncomputable local instance q6CollisionSumExactAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  Fintype.ofInjective (fun e => e.1) Subtype.val_injective

theorem mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) :
    let Xcount : ℕ := Nat.choose (n + 1) G
    let M : ℕ := 4 * Xcount ^ 2 + 1
    let Ω := (Fin (2 * n + 2) → ZMod M) × ZMod M
    (∑ ω : Ω,
      (let B := cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1
       ((B.product B).filter (fun p =>
        p.1 ≠ p.2 ∧
          (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card)) ≤
      2 *
        ((Nat.choose (2 * (n + 1)) L *
            Nat.choose (2 * (n + 1) - L) L) *
          Nat.choose (2 * G) G) *
        Xcount ^ 2 * S.card * M ^ (2 * n) := by
  sorry
