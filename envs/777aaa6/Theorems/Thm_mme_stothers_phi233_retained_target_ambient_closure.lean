-- Prove2me | Theorems.Thm_mme_stothers_phi233_retained_target_ambient_closure
-- name    : mme_stothers_phi233_retained_target_ambient_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:13:23.517752+00:00
-- url     : https://prove2.me/theorems/b3ba543c-5092-464f-bcd6-86879b4c937c
-- title:
--   Progression-free Phi233 retention preserves ambient completions
-- statement:
--   Fix one Phi233 affine hash state and an allowed field-label set S with no nonconstant three-term arithmetic progression. Whenever three retained exact-profile cyclic edges form a coordinatewise-supported mixture, there is a retained same-marginal ambient edge whose mode-zero, mode-one, and mode-two vertices are respectively those of the three input edges. Thus the hash restriction preserves precisely the completion property required by type-2 isolation pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356--360, specialized to the Phi233 same-marginal completion in Section 5, pp. 365--367.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_retention_data
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_AP
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
import Theorems.Thm_mme_stothers_phi233_cyclic_target_ambient_closure

set_option autoImplicit false

theorem mme_stothers_phi233_retained_target_ambient_closure
    {p N alpha beta gamma delta : ℕ}
    (S : Finset (ZMod p))
    (hSfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + b = 2 * c → a = c ∧ c = b)
    (q : MME.StothersFourth.Phi233.HashState p N) :
    ∀ x ∈ MME.StothersFourth.Phi233.retainedTarget p N alpha beta gamma delta S q,
      ∀ y ∈ MME.StothersFourth.Phi233.retainedTarget p N alpha beta gamma delta S q,
        ∀ z ∈ MME.StothersFourth.Phi233.retainedTarget p N alpha beta gamma delta S q,
          MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z →
            ∃ e ∈ MME.StothersFourth.Phi233.retainedAmbient p N alpha beta gamma delta S q,
              MME.StothersFourth.Phi233.cyclicModeWord e 0 =
                MME.StothersFourth.Phi233.cyclicModeWord x 0 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 1 =
                MME.StothersFourth.Phi233.cyclicModeWord y 1 ∧
              MME.StothersFourth.Phi233.cyclicModeWord e 2 =
                MME.StothersFourth.Phi233.cyclicModeWord z 2 := by
  sorry
