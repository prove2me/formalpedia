-- Prove2me | solution 3 for mme_stothers_phi134_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:09:08.587368+00:00
-- url     : https://prove2.me/submissions/4c4dbe2e-cd71-4ea2-a5f6-581885ac7d7c

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_stothers_phi134_cyclic_cofinal_finite_extraction

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 7 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 3 4)) tau V := by
  intro V hV hVlt
  obtain ⟨s, loss, hs, hloss, hextract⟩ :=
    mme_stothers_phi134_cyclic_cofinal_finite_extraction
      (K := K) tau htauLower htauUpper V hV hVlt
  exact mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (cyclicSymmetrization
      (MME.StothersFourth.cwFourthConstituent K 6 1 3 4))
    tau V hV s hs loss hloss hextract
