-- Prove2me | solution 1 for mme_stothers_lemma51_remaining_four_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:23:50.551764+00:00
-- url     : https://prove2.me/submissions/d0bc84af-6028-4752-9015-905cf9c2a34f

import Theorems.Thm_mme_stothers_phi125_cyclic_value
import Theorems.Thm_mme_stothers_phi134_cyclic_value
import Theorems.Thm_mme_stothers_phi224_cyclic_value
import Theorems.Thm_mme_stothers_phi233_cyclic_value

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
  exact ⟨
    mme_stothers_phi125_cyclic_value tau htauLower htauUpper,
    mme_stothers_phi134_cyclic_value tau htauLower htauUpper,
    mme_stothers_phi224_cyclic_value tau htauLower htauUpper,
    mme_stothers_phi233_cyclic_value tau htauLower htauUpper⟩
