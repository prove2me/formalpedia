-- Prove2me | Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le
-- name    : mme_ZMod_prime_affine_joint_fintype_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:55:51.741094+00:00
-- url     : https://prove2.me/theorems/0d304f51-7a7f-4655-92f6-97d4c76f24d3
-- title:
--   Prime affine joint-event bound over an arbitrary finite coordinate type
-- statement:
--   Let $I$ be a finite coordinate type with $|I|=n+1$ and let $p$ be prime. Any finite-state event which implies one nonconstant homogeneous linear equation in its weight vector and one equation fixing its affine offset has at most $p^n$ states. This is the structured-coordinate collision-fiber estimate used by cyclic type-2 hashing.
-- source:
--   Finite reindexing of the collision estimate in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360.

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open BigOperators

set_option autoImplicit false

theorem mme_ZMod_prime_affine_joint_fintype_card_le
    {p n : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = n + 1)
    (c : I → ZMod p) (j : I) (hc : c j ≠ 0)
    (offset : (I → ZMod p) → ZMod p)
    (joint : ((I → ZMod p) × ZMod p) → Prop)
    [DecidablePred joint]
    (hnormal : ∀ q, joint q →
      (∑ i, c i * q.1 i) = 0 ∧ q.2 = offset q.1) :
    ((Finset.univ.filter joint).card) ≤ p ^ n := by
  sorry
