-- Prove2me | solution 1 for mme_stothers_general_exact_address_block_value_of_class_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:46:50.968162+00:00
-- url     : https://prove2.me/submissions/e40d4206-c13f-4844-ae46-5049c9686385

import Theorems.Thm_mme_stothers_general_address_group_by_ordered_grade_types
import Theorems.Thm_mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ) (tau : ℝ)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ (m : ℕ) (a : MME.StothersFourth.GenExactOuterAddress base m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.genProfileCount base m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  intro m a W hW hstrict
  have hgroup :=
    mme_stothers_general_address_group_by_ordered_grade_types
      (K := K) base m a
  have hvalue :=
    mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
      (K := K) base tau hclass m W hW hstrict
  exact mme_HasTauValueAtLeast_mono_restrict hgroup.2 hvalue


