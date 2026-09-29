-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_pair_retention_card_le
-- name    : mme_stothers_phi233_cyclic_pair_retention_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:53:56.353055+00:00
-- url     : https://prove2.me/theorems/088e7427-a4ca-4fd8-86e9-382d6d74de56
-- title:
--   Pair-collision fiber bound for the Phi233 cyclic hash
-- statement:
--   Let p be prime and at least 7. If two distinct Phi233 cyclic ambient edges share a vertex in one of the three modes, then at most $$p^{6N}$$ affine hash states retain both edges in the same allowed label set S. Distinctness supplies a nonconstant collision equation in a mode where the edges differ, while sharing a vertex identifies their retained labels. This is the pair-incidence estimate used to delete high-degree vertices in the exceptional Phi233 extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356--360, and the Phi233 specialization in Section 5, pp. 365--367; shared-vertex pair-collision estimate.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_stothers_phi233_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_pair_retention_card_le
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (e f : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta)
    (S : Finset (ZMod p)) (hne : e ≠ f) (shared : Fin 3)
    (hshared : MME.StothersFourth.Phi233.cyclicModeWord e shared =
      MME.StothersFourth.Phi233.cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3)
        (a : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta) ↦
      MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  sorry
