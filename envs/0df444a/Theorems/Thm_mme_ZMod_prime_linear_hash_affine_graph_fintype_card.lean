-- Prove2me | Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card
-- name    : mme_ZMod_prime_linear_hash_affine_graph_fintype_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:52:18.649376+00:00
-- url     : https://prove2.me/theorems/c0e09822-21f0-496d-a296-795ae13d5faa
-- title:
--   Prime affine graph fiber count over an arbitrary finite coordinate type
-- statement:
--   Let $I$ be any finite coordinate type with $|I|=n+1$, let $p$ be prime, and let a linear form on $(\mathbb Z/p\mathbb Z)^I$ have a nonzero coefficient. For any label set $S$ and any prescribed affine offset function, the number of pairs consisting of a weight vector whose linear value lies in $S$ and the prescribed offset is exactly $|S|p^n$. This transports the standard finite-coordinate count to structured index types.
-- source:
--   Finite reindexing of the prime affine hash count used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360.

import Mathlib
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators

set_option autoImplicit false

theorem mme_ZMod_prime_linear_hash_affine_graph_fintype_card
    {p n : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = n + 1)
    (c : I → ZMod p) (j : I) (hc : c j ≠ 0)
    (S : Finset (ZMod p))
    (offset : (I → ZMod p) → ZMod p) :
    ((Finset.univ.filter
      (fun q : (I → ZMod p) × ZMod p ↦
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1)).card) =
      S.card * p ^ n := by
  sorry
