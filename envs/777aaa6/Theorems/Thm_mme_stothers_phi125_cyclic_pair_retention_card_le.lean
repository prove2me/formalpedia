-- Prove2me | Theorems.Thm_mme_stothers_phi125_cyclic_pair_retention_card_le
-- name    : mme_stothers_phi125_cyclic_pair_retention_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:13:41.122631+00:00
-- url     : https://prove2.me/theorems/da5f2c84-d0e5-4f77-b541-764187180a2c
-- title:
--   Collision-pair retention bound for the cyclic phi_125 hash
-- statement:
--   Let $e\ne f$ be two exact cyclic $\varphi_{125}$ edges of profile $(\alpha,\beta,\gamma)$, with $\alpha+\beta+\gamma=N$, and suppose they share one of their three mode words. For a prime $p\ge7$ and any label set $S\subseteq\mathbb Z/p\mathbb Z$, at most
--
--   $$
--   p^{6N}
--   $$
--
--   hash states retain both edges. Distinctness supplies a nonzero coefficient in another mode, while the shared mode forces the retained labels to agree; together these give one nonconstant linear equation plus the affine offset equation. This is the collision-fibre estimate used in the type-2 Salem--Spencer pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 collision estimate, printed pp. 359-361, specialized to the phi_125 profile in Lemma 5.1(ii), pp. 364-365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_cyclic_hash_data
import Theorems.Thm_mme_stothers_phi125_cyclic_mode_word_tuple_injective
import Theorems.Thm_mme_stothers_phi125_distinct_mode_code_difference_has_nonzero_coefficient
import Theorems.Thm_mme_stothers_phi125_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_ZMod_prime_affine_joint_fintype_card_le

open BigOperators
open MME.StothersFourth.Phi125

set_option autoImplicit false

theorem mme_stothers_phi125_cyclic_pair_retention_card_le
    {p N alpha beta gamma : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : alpha + beta + gamma = N)
    (e f : CyclicExactEdge N alpha beta gamma) (S : Finset (ZMod p))
    (hne : e ≠ f) (shared : Fin 3)
    (hshared : cyclicModeWord e shared = cyclicModeWord f shared) :
    let I := (Fin 3 × Fin (2 * N)) ⊕ Unit
    let weights := fun w : I → ZMod p ↦
      fun r j ↦ w (Sum.inl (r, j))
    let shift := fun w : I → ZMod p ↦ w (Sum.inr ())
    let H := fun (q : (I → ZMod p) × ZMod p)
        (i : Fin 3) (a : CyclicExactEdge N alpha beta gamma) ↦
      cyclicAffineHash p N alpha beta gamma
        (weights q.1) (shift q.1) ((6 : ZMod p)⁻¹ * q.2) i a
    let retain := fun (q : (I → ZMod p) × ZMod p)
        (a : CyclicExactEdge N alpha beta gamma) ↦
      ∃ s ∈ S, ∀ i : Fin 3, H q i a = s
    ((Finset.univ.filter (fun q ↦ retain q e ∧ retain q f)).card) ≤
      p ^ (6 * N) := by
  sorry
