-- Prove2me | Theorems.Thm_mme_stothers_phi233_named_hash_fiber_package
-- name    : mme_stothers_phi233_named_hash_fiber_package
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:24:50.483987+00:00
-- url     : https://prove2.me/theorems/148b31d7-fc95-4f69-bc33-d7ccc277ba7c
-- title:
--   Exact Phi233 hash fibers in the retained-family interface
-- statement:
--   For the cyclic Phi233 exact-profile target and same-marginal ambient families, every target edge is retained by exactly |S| p^(6N) affine hash states. Every distinct target--ambient pair sharing at least one cyclic mode vertex is jointly retained by at most p^(6N) states. These are the exact uniform fiber estimates required by sharp induced-family extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, specialized to the exceptional Phi233 constituent.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_retention_data
import Definitions.Def_mme_stothers_phi233_hash_state_instances
import Theorems.Thm_mme_stothers_phi233_cyclic_edge_retention_card
import Theorems.Thm_mme_stothers_phi233_cyclic_pair_retention_card_le

open MME.StothersFourth.Phi233

set_option autoImplicit false

theorem mme_stothers_phi233_named_hash_fiber_package
    {p N alpha beta gamma delta : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (S : Finset (ZMod p))
    [DecidableEq (MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta)]
    [DecidableEq (MME.StothersFourth.Phi233.CyclicModeWord N)]
    [DecidableRel (MME.StothersFourth.Phi233.Retained p N alpha beta gamma delta S)] :
    (∀ e ∈ MME.StothersFourth.Phi233.targetFinset N alpha beta gamma delta,
      ((Finset.univ : Finset (MME.StothersFourth.Phi233.HashState p N)).filter
        (fun q ↦ MME.StothersFourth.Phi233.Retained p N alpha beta gamma delta S q e)).card =
          S.card * p ^ (6 * N)) ∧
    (∀ ef ∈ ((MME.StothersFourth.Phi233.targetFinset N alpha beta gamma delta ×ˢ
        MME.StothersFourth.Phi233.ambientFinset N alpha beta gamma delta).filter (fun ef ↦
          ef.1 ≠ ef.2 ∧ ∃ i : Fin 3,
            MME.StothersFourth.Phi233.cyclicModeWord ef.1 i =
              MME.StothersFourth.Phi233.cyclicModeWord ef.2 i)),
      ((Finset.univ : Finset (MME.StothersFourth.Phi233.HashState p N)).filter
        (fun q ↦ MME.StothersFourth.Phi233.Retained p N alpha beta gamma delta S q ef.1 ∧
          MME.StothersFourth.Phi233.Retained p N alpha beta gamma delta S q ef.2)).card ≤
            p ^ (6 * N)) := by
  sorry
