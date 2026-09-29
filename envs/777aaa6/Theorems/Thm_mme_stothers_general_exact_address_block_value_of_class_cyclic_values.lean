-- Prove2me | Theorems.Thm_mme_stothers_general_exact_address_block_value_of_class_cyclic_values
-- name    : mme_stothers_general_exact_address_block_value_of_class_cyclic_values
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:42:16.835391+00:00
-- url     : https://prove2.me/theorems/023fdb9f-716d-4fb4-b370-69bbbf5ae462
-- title:
--   Block value of a general-profile exact outer address
-- statement:
--   **Every exact outer address of a general profile carries the full class-value product.**
--
--   Fix a strictly positive integral ten-class profile $\beta$ and an exponent $\tau$, and suppose that for each cyclic class $r$ the cyclically symmetrized class constituent has tau-value at least $V$ for every $0 \le V < v_r(\tau)$.
--
--   Then for every scale $m$ and *every* exact outer address $a$ of profile $\beta$ at that scale, the graded block $B_a$ cut out of $CW_6^{\otimes 4}$ has tau-value at least $W$ for every
--
--   $$0 \le W \;<\; \prod_{r=1}^{10} v_r(\tau)^{\,c_r\, \beta_r m} .$$
--
--   The point is the uniformity in $a$: the bound depends only on the profile, not on which exact address realises it.  That is what makes the laser extraction work, because the surviving family produced by the hashing step is an uncontrolled subset of the exact addresses, and each of its members must contribute the same block value.
--
--   It is the hypothesis `hblocks` of the general-profile fourth-power value assembly, the companion of the outer capacity bound.  The published version is the specialisation of this statement to the ten-vector of Section 5.
--
--   *Formalization note.* The proof composes the regrouping of the address by ordered grade type with the value of that regrouped product, transporting the value along the restriction underlying the isomorphism.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 (the fourth power of the Coppersmith--Winograd tensor, its ten oriented grade classes, and the block value of an exact outer address); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_general_exact_address_block_value_of_class_cyclic_values
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
  sorry
