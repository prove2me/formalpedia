-- Prove2me | Theorems.Thm_mme_stothers_phi233_concrete_fractional_extraction
-- name    : mme_stothers_phi233_concrete_fractional_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:22:12.476097+00:00
-- url     : https://prove2.me/theorems/681dc13a-338c-4c7f-9b7a-813574b9518c
-- title:
--   Concrete fractional type-2 extraction for cyclic phi_233
-- statement:
--   Let $p\geq7$ be prime, let the phi_233 profile be valid and nonempty, and let $S\subseteq\mathbb Z/p\mathbb Z$ contain no nontrivial three-term arithmetic progression. Assume the same-marginal/exact-profile completion ratio is at most $R$ and the normalized margin $p^2\ell+3R^3D_*\leq|S|$ holds, where $D_*$ is the exact cyclic mode degree. Then some affine hash state retains an isolated target family containing at least an $\ell$ fraction of all exact cyclic target edges. The retained family is injective in every mode and every coordinatewise-supported mixed triple is diagonal, so it is ready for the tensor direct-sum realization.
-- source:
--   The affine hashing, progression-free selection, and type-2 pruning argument in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Sections 3 and 5.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_hash_state_card
import Theorems.Thm_mme_stothers_phi233_cyclic_relative_degree_package
import Theorems.Thm_mme_stothers_phi233_cyclic_edge_retention_card
import Theorems.Thm_mme_stothers_phi233_cyclic_pair_retention_card_le
import Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
import Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem mme_stothers_phi233_concrete_fractional_extraction
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress N alpha beta gamma delta)
    (S : Finset (ZMod p))
    (hSfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x + y = 2 * z → x = z ∧ z = y)
    (R ell : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card (MME.StothersFourth.Phi233.MarginalAddress N alpha beta gamma delta) : ℝ) ≤
        R * (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress N alpha beta gamma delta) : ℝ))
    (hmargin :
      ((p ^ 2 : ℕ) : ℝ) * ell +
          3 * R ^ 3 *
            ((∏ l : Fin 3,
              Nat.card
                {b : MME.StothersFourth.Phi233.ExactProfileAddress N alpha beta gamma delta //
                  b.1.1 l = a.1.1 l}) : ℝ) ≤
        (S.card : ℝ)) :
    ∃ q : MME.StothersFourth.Phi233.HashState p N,
      ∃ kept : Finset (MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta),
        kept ⊆ MME.StothersFourth.Phi233.retainedTarget p N alpha beta gamma delta S q ∧
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ MME.StothersFourth.Phi233.cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        ((MME.StothersFourth.Phi233.targetFinset N alpha beta gamma delta).card : ℝ) * ell ≤
          (kept.card : ℝ) := by
  sorry
