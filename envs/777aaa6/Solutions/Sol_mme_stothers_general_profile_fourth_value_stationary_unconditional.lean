-- Prove2me | solution 1 for mme_stothers_general_profile_fourth_value_stationary_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-10T05:56:41.643767+00:00
-- url     : https://prove2.me/submissions/37562180-eee2-4980-becf-d646795cc752

import Theorems.Thm_mme_stothers_general_profile_fourth_value_stationary
import Theorems.Thm_mme_stothers_elementary_table1_cyclic_values
import Theorems.Thm_mme_stothers_lemma51_recursive_values
import Theorems.Thm_mme_stothers_fourth_support_and_classes

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) →
      HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  have helem :=
    mme_stothers_elementary_table1_cyclic_values (K := K) tau htauLower htauUpper
  have hrec :=
    mme_stothers_lemma51_recursive_values (K := K) tau htauLower htauUpper
  refine mme_stothers_general_profile_fourth_value_stationary
    base bstar tau hbase hbstar hsame hInN ?_ ?_
  · intro sigma hnonzero
    have hsupp := (mme_stothers_fourth_support_and_classes (K := K)).1 sigma
    by_contra hsum
    exact hnonzero (hsupp.mpr hsum)
  · intro r V hV hstrict
    fin_cases r
    · simpa [MME.StothersFourth.classRep] using helem (0 : Fin 5) V hV hstrict
    · simpa [MME.StothersFourth.classRep] using helem (1 : Fin 5) V hV hstrict
    · simpa [MME.StothersFourth.classRep] using helem (2 : Fin 5) V hV hstrict
    · simpa [MME.StothersFourth.classRep] using helem (3 : Fin 5) V hV hstrict
    · simpa [MME.StothersFourth.classRep] using helem (4 : Fin 5) V hV hstrict
    · simpa [MME.StothersFourth.classRep] using hrec.1 V hV hstrict
    · simpa [MME.StothersFourth.classRep] using hrec.2.1 V hV hstrict
    · simpa [MME.StothersFourth.classRep] using hrec.2.2.1 V hV hstrict
    · simpa [MME.StothersFourth.classRep] using hrec.2.2.2.1 V hV hstrict
    · simpa [MME.StothersFourth.classRep] using hrec.2.2.2.2 V hV hstrict
