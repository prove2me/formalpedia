-- Prove2me | solution 2 for mme_stothers_phi224_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T05:50:55.470951+00:00
-- url     : https://prove2.me/submissions/e33fd9be-dead-4f64-be89-18a1b0dc1b16

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_lemma51_remaining_four_values

open MME
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 8 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V := by
  rcases mme_stothers_lemma51_remaining_four_values (K := K) tau htauLower htauUpper with
    ⟨h6, h7, h8, h9⟩
  exact h8 
