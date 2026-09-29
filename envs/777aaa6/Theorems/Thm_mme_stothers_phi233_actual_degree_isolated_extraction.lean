-- Prove2me | Theorems.Thm_mme_stothers_phi233_actual_degree_isolated_extraction
-- name    : mme_stothers_phi233_actual_degree_isolated_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T04:00:51.131194+00:00
-- url     : https://prove2.me/theorems/f703ee05-4499-43c3-b069-c06e9396b351
-- title:
--   Actual-degree isolated extraction for cyclic phi_233
-- statement:
--   Fix a valid cyclic $\varphi_{233}$ exact profile and an exact address $a$. Let $D$ be the product of the three ambient fixed-mode star cardinalities at $a$. For a prime $p\ge7$, let $S\subseteq\mathbb F_p$ contain no nonconstant three-term arithmetic progression. If $|S|\ge6D$, then some affine hash state admits a cyclic target subfamily $K$ that is ambient-isolated, injective in each of its three mode words, and whose every coordinatewise-supported triple is diagonal. Moreover,
--
--   $$
--   |K|\ge |\mathcal T|\frac{|S|}{2p^2},
--   $$
--
--   where $\mathcal T$ is the full exact-profile cyclic target family. Ambient isolation is the missing hypothesis required by the isolated kept-profile value theorem, so this statement is the direct finite bridge from Behrend selection to tensor realization.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Sections 3 and 5.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_hash_state_card
import Theorems.Thm_mme_stothers_phi233_uniform_cyclic_mode_degrees
import Theorems.Thm_mme_stothers_phi233_named_hash_fiber_package
import Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities
import Theorems.Thm_mme_type2_uniform_hash_retention_aggregate_incidence
import Theorems.Thm_mme_type2_hash_loss_budget_of_cardinality_ratio_and_incidence
import Theorems.Thm_mme_finite_collision_budget_averaging_real
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open MME BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false

theorem mme_stothers_phi233_actual_degree_isolated_extraction
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : ExactProfileAddress N alpha beta gamma delta)
    (S : Finset (ZMod p))
    (hSfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x + y = 2 * z → x = z ∧ z = y)
    (hlarge :
      6 *
          ((∏ l : Fin 3,
            Nat.card
              {b : MarginalAddress N alpha beta gamma delta //
                b.1 l = a.1.1 l}) : ℝ) ≤
        (S.card : ℝ)) :
    ∃ q : HashState p N,
      ∃ kept : Finset (CyclicAmbientEdge N alpha beta gamma delta),
        kept ⊆ retainedTarget p N alpha beta gamma delta S q ∧
        (∀ e ∈ retainedAmbient p N alpha beta gamma delta S q,
          (∀ i : Fin 3, ∃ f ∈ kept,
            cyclicModeWord e i = cyclicModeWord f i) →
          e ∈ kept) ∧
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦ cyclicModeWord e.1 i)) ∧
        (∀ x y z : kept,
          CyclicCoordinatewiseSupported x.1 y.1 z.1 →
            x = y ∧ y = z) ∧
        ((targetFinset N alpha beta gamma delta).card : ℝ) *
            ((S.card : ℝ) / (2 * ((p ^ 2 : ℕ) : ℝ))) ≤
          (kept.card : ℝ) := by
  sorry
