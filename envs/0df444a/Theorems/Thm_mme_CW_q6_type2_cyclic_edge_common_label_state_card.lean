-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_edge_common_label_state_card
-- name    : mme_CW_q6_type2_cyclic_edge_common_label_state_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:57:51.808518+00:00
-- url     : https://prove2.me/theorems/719cc6b6-61d2-4f85-93a2-05f244ba17cd
-- title:
--   Exact common-label retention count for one cyclic q=6 type-2 edge
-- statement:
--   Let $p\ge 7$ be prime and $N>0$. Give the cyclic q=6 type-2 hash its $6N$ genuine weight coordinates, one harmless dummy weight, and one affine parameter, with the latter rescaled by $6^{-1}$. For every exact cyclic edge and label set $S\subseteq\mathbb Z/p\mathbb Z$, exactly $|S|p^{6N}$ hash states send all three mode vertices to one common label in $S$. This is the uniform single-edge incidence count used in the type-2 hashing budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; exact single-edge Salem--Spencer hash incidence.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_hash_mode_code_has_nonzero_coefficient
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_fintype_card

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_edge_common_label_state_card
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hN : 0 < N)
    (e : CWQ6Type2CyclicEdge N L G) (S : Finset (ZMod p)) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let H := fun (q : (I → ZMod p) × ZMod p) (i : Fin 3) ↦
      cwQ6Type2CyclicAffineHash p N L G
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) i e
    ((Finset.univ.filter
      (fun q ↦ ∃ s ∈ S, ∀ i : Fin 3, H q i = s)).card) =
      S.card * p ^ (6 * N) := by
  sorry
