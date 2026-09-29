-- Prove2me | Theorems.Thm_mme_stothers_fixed_ordered_grade_product_value_of_class_cyclic_values
-- name    : mme_stothers_fixed_ordered_grade_product_value_of_class_cyclic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:09:14.776999+00:00
-- url     : https://prove2.me/theorems/2e32b3f3-b71f-49c8-bc7f-46916d2cd3e8
-- title:
--   Value the canonical ordered-grade product from ten cyclic class values
-- statement:
--   Fix $\tau$ and suppose the cyclic symmetrization of each Table-1 class representative attains every nonnegative strict lower value below $v_r(\tau)$. At integral scale $m$, form the canonical product over all 729 ordered grade triples, taking the corresponding fourth-power block with its prescribed joint multiplicity. This product attains every nonnegative value strictly below $$\prod_{r=0}^{9}v_r(\tau)^{n_r c_r(m)}.$$ This theorem contains exactly the finite Table-1 orbit step: discard the zero-multiplicity unsupported types, partition the 45 supported ordered triples into fifteen cyclic orbits, transfer the five reverse-orientation orbits through mode permutations, and apply finite strict-value synchronization. It is independent of the choice of an outer address.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Table 1 and the constituent-value substitution in Theorem 5.3, printed pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_ordered_grade_product_value_of_class_cyclic_values
    {K : Type u} [Field K]
    (tau : ℝ)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ (m : ℕ) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
        classical
        exact (Fintype.equivFin (Fin 3 → Fin 9)).trans
          (finCongr (by simp only [Fintype.card_fun, Fintype.card_fin]; norm_num))
      HasTauValueAtLeast
        (TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.fixedJointMultiplicity m (e.symm s))))
        tau W := by
  sorry
