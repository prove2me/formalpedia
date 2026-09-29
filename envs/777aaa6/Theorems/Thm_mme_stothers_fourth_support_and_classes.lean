-- Prove2me | Theorems.Thm_mme_stothers_fourth_support_and_classes
-- name    : mme_stothers_fourth_support_and_classes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-29T00:19:50.682664+00:00
-- url     : https://prove2.me/theorems/effb313e-941a-47fa-9c97-5f63295720b4
-- title:
--   Section 5 and Table 1: fourth-power support and ten classes
-- statement:
--   Let $K$ be an arbitrary field. In the canonical nine-grading of the literal fourth power $CW_6^{\otimes4}$:
--
--   1. every block whose three mode grades do not sum to $8$ has zero block tensor;
--   2. exactly $45$ grade triples sum to $8$;
--   3. every such triple belongs to a unique permutation orbit represented by one of
--      $008,017,026,035,044,116,125,134,224,233$; and
--   4. the orbit represented by class $i$ has cardinality $3n_i$, where
--      $n=(1,2,2,2,1,1,2,2,1,1)$.
--
--   This is the literal fourth-power decomposition underlying Section 5 and Table 1; it does not replace overlapping blocks by an external direct sum.
-- source:
--   Davie and Stothers (2013), Section 5, paragraph preceding Lemma 5.1 and Table 1, printed pp. 363 and 367, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fourth_support_and_classes
    {K : Type u} [Field K] :
    (∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8) ∧
    Fintype.card
        {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} = 45 ∧
    (∀ sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8},
      ∃! r : Fin 10,
        MME.StothersFourth.sameOrbit sigma.1
          (MME.StothersFourth.classRep r)) ∧
    (∀ r : Fin 10,
      Fintype.card
          {sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} //
            MME.StothersFourth.sameOrbit sigma.1
              (MME.StothersFourth.classRep r)} =
        3 * MME.StothersFourth.classMultiplicity r) := by
  sorry
