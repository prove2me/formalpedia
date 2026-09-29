-- Prove2me | solution 2 for mme_stothers_lemma51_remaining_four_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T01:05:57.947389+00:00
-- url     : https://prove2.me/submissions/6c3fc692-784e-4a35-9439-f9a66141aad9

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_lemma51_recursive_values

open MME

universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 6 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 8 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 2 4)) tau V) ∧
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 9 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)) tau V) := by
  rcases mme_stothers_lemma51_recursive_values (K := K) tau htauLower htauUpper with
    ⟨h5, h6, h7, h8, h9⟩
  exact ⟨h6, h7, h8, h9⟩
