-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_edge_retention_card
-- name    : mme_stothers_phi233_cyclic_edge_retention_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:50:34.171499+00:00
-- url     : https://prove2.me/theorems/62e0329e-e0ba-4b17-8e27-e1c8f7bddeb1
-- title:
--   Exact one-edge retention count for the Phi233 cyclic hash
-- statement:
--   Let p be a prime at least 7, let e be a Phi233 cyclic ambient edge of length 2N, and let S be a finite set of allowed hash labels. For the cyclic affine hash with 6N+1 independent weight coordinates (including its common shift) and one offset coordinate, the exact number of states that assign one common label in S to all three vertices of e is $$|S|p^{6N}.$$ The common-shift coordinate makes this exact formula valid even at N=0. This is the one-edge incidence input for the Phi233 Salem--Spencer pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356--360, and the Phi233 specialization in Section 5, pp. 365--367; exact one-edge hash-state count.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_AP
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_edge_retention_card
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  sorry
