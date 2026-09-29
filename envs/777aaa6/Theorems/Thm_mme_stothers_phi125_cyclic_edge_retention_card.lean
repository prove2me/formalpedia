-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_edge_retention_card
-- name    : mme_stothers_phi125_cyclic_edge_retention_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:14:09.115527+00:00
-- url     : https://prove2.me/theorems/abc2a96e-1719-45bf-b0d7-5c8fe1c73b6d
-- title:
--   Exact one-edge retention count for the cyclic phi_125 hash
-- statement:
--   Fix a prime $p\ge 7$, an exact cyclic $\varphi_{125}$ edge of length $2N$, and a label set $S\subseteq\mathbb Z/p\mathbb Z$. Use the Davie--Stothers cyclic affine hash with $6N+2$ random parameters. The number of states in which all three vertex hashes of this edge agree at a label in $S$ is exactly
--
--   $$
--   |S|p^{6N}.
--   $$
--
--   The theorem is the exact single-edge incidence count needed before double-counting and collision pruning in the type-2 extraction. The inverse of $6$ is valid because $p\ge7$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 type-2 hashing calculation, printed pp. 359-361, specialized to the phi_125 profile of Lemma 5.1(ii), pp. 364-365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_AP
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_edge_retention_card
    {p N alpha beta gamma : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e : CyclicExactEdge N alpha beta gamma) (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cyclicAffineHash p N alpha beta gamma
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  sorry
