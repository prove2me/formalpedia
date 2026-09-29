-- Prove2me | solution 1 for mme_stothers_phi134_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T05:44:18.276931+00:00
-- url     : https://prove2.me/submissions/7628a37c-63e3-418b-be3e-57f90b062368

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_lemma51_remaining_four_values

open MME
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V := by
  rcases mme_stothers_lemma51_remaining_four_values (K := K) tau htauLower htauUpper with
    ⟨h6, h7, h8, h9⟩
  exact h7
