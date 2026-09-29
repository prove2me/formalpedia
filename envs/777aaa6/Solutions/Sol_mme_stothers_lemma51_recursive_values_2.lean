-- Prove2me | solution 2 for mme_stothers_lemma51_recursive_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T06:20:24.791294+00:00
-- url     : https://prove2.me/submissions/959b07dd-fe50-421b-ae14-e2a42699b08a

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_phi116_outer_hashing_value
import Theorems.Thm_mme_stothers_phi116_four_edge_support
import Theorems.Thm_mme_stothers_phi116_outer_component_restrictions
import Theorems.Thm_mme_stothers_lemma51_remaining_four_values

open MME
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    (∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V) ∧
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
  have h5 := mme_stothers_phi116_outer_hashing_value (K := K) tau htauLower htauUpper
    (mme_stothers_phi116_four_edge_support (K := K))
    (mme_stothers_phi116_outer_component_restrictions (K := K))
  have hrest := mme_stothers_lemma51_remaining_four_values (K := K) tau htauLower htauUpper
  exact ⟨h5, hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2⟩
