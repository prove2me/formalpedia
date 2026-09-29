-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_exact_edge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:14:30.686702+00:00
-- url     : https://prove2.me/submissions/7a1cf9b6-6f30-47dc-9838-38577441f78e

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_exact_profile_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Nat.card
        (MME.StothersFourth.Phi125.CyclicExactEdge
          N alpha beta gamma) =
      ((2 * N).factorial /
        ∏ r : Fin 6,
          (MME.StothersFourth.Phi125.profileMultiplicity
            alpha beta gamma r).factorial) ^ (3 : ℕ) := by
  let A := MME.StothersFourth.Phi125.ExactProfileWord
    N alpha beta gamma
  have hprod :
      Nat.card (A × (A × A)) = Nat.card A * (Nat.card A * Nat.card A) := by
    rw [Nat.card_prod, Nat.card_prod]
  change Nat.card (A × (A × A)) = _
  rw [hprod, mme_stothers_phi125_exact_profile_card N alpha beta gamma hsum]
  ring
