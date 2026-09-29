-- Prove2me | solution 1 for mme_stothers_lemma51_recursive_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:37:20.017964+00:00
-- url     : https://prove2.me/submissions/bae62ad8-063f-4f55-8775-4d3f96fbd77e

import Theorems.Thm_mme_stothers_phi116_four_edge_support
import Theorems.Thm_mme_stothers_phi116_outer_component_restrictions
import Theorems.Thm_mme_stothers_phi116_outer_hashing_value
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
  refine ⟨?_, mme_stothers_lemma51_remaining_four_values
    tau htauLower htauUpper⟩
  exact mme_stothers_phi116_outer_hashing_value
    tau htauLower htauUpper
      (mme_stothers_phi116_four_edge_support (K := K))
      (mme_stothers_phi116_outer_component_restrictions (K := K))
