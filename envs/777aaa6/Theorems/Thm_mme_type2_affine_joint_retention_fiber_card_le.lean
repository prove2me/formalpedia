-- Prove2me | Theorems.Thm_mme_type2_affine_joint_retention_fiber_card_le
-- name    : mme_type2_affine_joint_retention_fiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:14:08.55497+00:00
-- url     : https://prove2.me/theorems/5b43788f-9fbf-4d94-9c6f-81210249970c
-- title:
--   Prime affine bound for a type-2 joint-retention collision fiber
-- statement:
--   Let a joint-retention event over an affine hash state in $(\mathbb Z/p\mathbb Z)^{n+1}\times\mathbb Z/p\mathbb Z$ imply one nonconstant homogeneous linear equation in the weight coordinates and one equation fixing the affine offset. Then the event contains at most $$p^n$$ states. This is the uniform simultaneous-retention bound for each target--ambient collision pair in the type-2 hash.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360; prime affine collision-fiber estimate.

import Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le

open BigOperators

set_option autoImplicit false

theorem mme_type2_affine_joint_retention_fiber_card_le
    {p n : ℕ} [Fact p.Prime]
    (c : Fin (n + 1) → ZMod p) (j : Fin (n + 1)) (hc : c j ≠ 0)
    (offset : (Fin (n + 1) → ZMod p) → ZMod p)
    (joint : ((Fin (n + 1) → ZMod p) × ZMod p) → Prop)
    [DecidablePred joint]
    (hnormal : ∀ q, joint q → (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1) :
    ((Finset.univ.filter joint).card) ≤ p ^ n := by
  sorry
