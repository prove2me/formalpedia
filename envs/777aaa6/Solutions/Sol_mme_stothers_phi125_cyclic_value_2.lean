-- Prove2me | solution 2 for mme_stothers_phi125_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T05:50:54.185412+00:00
-- url     : https://prove2.me/submissions/107bfad1-61fb-46b2-925a-2229579f66e2

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_lemma51_remaining_four_values

open MME
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 6 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)) tau V := by
  rcases mme_stothers_lemma51_remaining_four_values (K := K) tau htauLower htauUpper with
    ⟨h6, h7, h8, h9⟩
  exact h6
