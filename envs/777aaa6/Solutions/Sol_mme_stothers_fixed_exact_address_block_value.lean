-- Prove2me | solution 1 for mme_stothers_fixed_exact_address_block_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:49:03.718562+00:00
-- url     : https://prove2.me/submissions/35626423-cbfc-4eb2-a710-f4d4c87a3bb3

import Theorems.Thm_mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
import Theorems.Thm_mme_stothers_elementary_table1_cyclic_values
import Theorems.Thm_mme_stothers_lemma51_recursive_values

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

/-! Exact-address values split cleanly into finite orbit bookkeeping, the
five elementary Table-1 rows, and the five recursive rows of Lemma 5.1. -/

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau)
    (htauUpper : 3 * tau ≤ 3) :
    ∀ (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  have helem :=
    mme_stothers_elementary_table1_cyclic_values
      (K := K) tau htauLower htauUpper
  have hrec :=
    mme_stothers_lemma51_recursive_values
      (K := K) tau htauLower htauUpper
  apply mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
    tau
  intro r V hV hstrict
  fin_cases r
  · simpa [MME.StothersFourth.classRep] using
      helem (0 : Fin 5) V hV hstrict
  · simpa [MME.StothersFourth.classRep] using
      helem (1 : Fin 5) V hV hstrict
  · simpa [MME.StothersFourth.classRep] using
      helem (2 : Fin 5) V hV hstrict
  · simpa [MME.StothersFourth.classRep] using
      helem (3 : Fin 5) V hV hstrict
  · simpa [MME.StothersFourth.classRep] using
      helem (4 : Fin 5) V hV hstrict
  · simpa [MME.StothersFourth.classRep] using hrec.1 V hV hstrict
  · simpa [MME.StothersFourth.classRep] using hrec.2.1 V hV hstrict
  · simpa [MME.StothersFourth.classRep] using hrec.2.2.1 V hV hstrict
  · simpa [MME.StothersFourth.classRep] using hrec.2.2.2.1 V hV hstrict
  · simpa [MME.StothersFourth.classRep] using hrec.2.2.2.2 V hV hstrict

