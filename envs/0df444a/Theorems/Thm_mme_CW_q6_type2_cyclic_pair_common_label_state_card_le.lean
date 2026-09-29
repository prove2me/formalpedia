-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_pair_common_label_state_card_le
-- name    : mme_CW_q6_type2_cyclic_pair_common_label_state_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:05:00.328637+00:00
-- url     : https://prove2.me/theorems/9a09670f-343a-4b12-9bc2-f06cb1381435
-- title:
--   Pair-collision state bound for cyclic q=6 type-2 edges
-- statement:
--   Let two distinct cyclic q=6 type-2 edges share a vertex in one mode. Under the padded affine hash used for type-2 pruning, the number of hash states that retain both edges with a common label from an arbitrary set S is at most p^(6N). This is the exact pair-collision input for the cyclic hash budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; cyclic pair-collision pruning estimate.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_CW_q6_type2_cyclic_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_pair_common_label_state_card_le
    {p N L G : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : CWQ6Type2CyclicEdge N L G) (S : Finset (ZMod p))
    (hne : e ≠ f) (shared : Fin 3)
    (hshared : cwQ6Type2CyclicModeWord e shared =
      cwQ6Type2CyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CWQ6Type2CyclicEdge N L G) ↦
      cwQ6Type2CyclicAffineHash p N L G
        (weights q.1, (6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CWQ6Type2CyclicEdge N L G) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  sorry
