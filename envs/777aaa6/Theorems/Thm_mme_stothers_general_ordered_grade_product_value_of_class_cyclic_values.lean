-- Prove2me | Theorems.Thm_mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
-- name    : mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:42:29.223348+00:00
-- url     : https://prove2.me/theorems/900c897a-a9ac-41c9-a82e-6c73af84962a
-- title:
--   Value of the ordered grade product from the ten class values (general profile)
-- statement:
--   **The ordered grade product inherits the product of the ten class values.**
--
--   Fix a strictly positive integral ten-class profile $\beta$ and an exponent $\tau$.  Suppose that for each of the ten cyclic classes $r$ the cyclically symmetrized class constituent has tau-value at least $V$ for every $0 \le V < v_r(\tau)$, where $v_r(\tau)$ is the class value of Lemma 5.1.
--
--   Then for every scale $m$ the ordered product of the $729$ grade blocks with the profile's joint multiplicities has tau-value at least $W$ for every
--
--   $$0 \le W \;<\; \prod_{r=1}^{10} v_r(\tau)^{\,c_r\, \beta_r m},$$
--
--   with $c_r$ the size of the cyclic class $r$ inside the fifteen oriented classes.
--
--   This is the value half of the Davie--Stothers block analysis: after the address block has been regrouped by grade type, the value of the product is bounded below by the product of the individual class values, each raised to the number of positions of that class.  The exponent $c_r \beta_r m$ is exactly the number of address positions whose ordered grade triple lies in the cyclic orbit of the class representative $\rho_r$.
--
--   The published version fixes $\beta$ to the ten-vector of Section 5; this statement holds for every positive integral profile, which is what an optimisation over profiles requires.
--
--   *Formalization note.* Endpoints are strict on both sides, so the statement composes with itself and with the multiplicativity of the tau-value under Kronecker products.  Three of the fifteen oriented classes are the swaps of their cyclic representatives and are handled by the swap-invariance of the tau-value.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 (the fourth power of the Coppersmith--Winograd tensor, its ten oriented grade classes, and the block value of an exact outer address); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_general_ordered_grade_product_value_of_class_cyclic_values
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
    ∀ (m : ℕ) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.genProfileCount base m r)) →
      let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
        classical
        simpa only [Fintype.card_fun, Fintype.card_fin, pow_succ,
          pow_zero, mul_one] using
          (Fintype.equivFin (Fin 3 → Fin 9))
      HasTauValueAtLeast
        (TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.genJointMultiplicity base m (e.symm s))))
        tau W := by
  sorry
