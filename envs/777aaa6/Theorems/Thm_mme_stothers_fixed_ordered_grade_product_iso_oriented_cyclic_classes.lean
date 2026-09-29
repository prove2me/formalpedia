-- Prove2me | Theorems.Thm_mme_stothers_fixed_ordered_grade_product_iso_oriented_cyclic_classes
-- name    : mme_stothers_fixed_ordered_grade_product_iso_oriented_cyclic_classes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:34:11.095071+00:00
-- url     : https://prove2.me/theorems/7a5106ff-f352-4d14-8233-2f21ab1d9831
-- title:
--   Regroup the fixed fourth-power product into fifteen oriented cyclic classes
-- statement:
--   At fixed integral profile scale $m$, the ordered Kronecker product of all $9^3$ literal fourth-power grade blocks, each repeated with its exact joint multiplicity, is tensor-isomorphic to the product over the fifteen **oriented** three-element cyclic orbits in Davie--Stothers Table 1.  The multiplicity of an oriented orbit is the fixed profile count of its underlying Table-1 class.  Keeping both orientations for each six-element permutation class is essential: the second orientation is mode-swapped rather than a duplicate ordered tensor.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_oriented_cyclic_classes

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_ordered_grade_product_iso_oriented_cyclic_classes
    {K : Type u} [Field K] (m : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 15 (fun t ↦
        (cyclicSymmetrization
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (MME.StothersFourth.fixedOrientedRep t))).kronPow
              (MME.StothersFourth.fixedProfileCount m
                (MME.StothersFourth.fixedOrientedClass t))))
      (let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
          classical
          simpa only [Fintype.card_fun, Fintype.card_fin, pow_succ,
            pow_zero, mul_one] using
            (Fintype.equivFin (Fin 3 → Fin 9))
        TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.fixedJointMultiplicity m (e.symm s)))) := by
  sorry
