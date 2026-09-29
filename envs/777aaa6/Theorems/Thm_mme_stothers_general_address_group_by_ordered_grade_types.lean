-- Prove2me | Theorems.Thm_mme_stothers_general_address_group_by_ordered_grade_types
-- name    : mme_stothers_general_address_group_by_ordered_grade_types
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:42:27.619106+00:00
-- url     : https://prove2.me/theorems/8f04bb8c-b783-40ce-9323-76e24d9ee767
-- title:
--   Regrouping a general-profile exact address by ordered grade type
-- statement:
--   **An exact outer address, regrouped by its ordered grade triples.**
--
--   Fix a strictly positive integral ten-class profile $\beta$ and a scale $m$.  An *exact outer address* of length $N = 3 D m$, where $D = \sum_r c_r \beta_r$, is a word $a$ in the nine grades in each of the three modes whose ordered grade triple $\sigma(k) = (a_0(k), a_1(k), a_2(k))$ realises each of the $729$ possible triples exactly $\mu_\beta(m,\sigma)$ times, where $\mu_\beta(m,\sigma)$ is the joint multiplicity attached to the profile.
--
--   The graded block that such an address cuts out of the fourth power is then isomorphic to the ordered Kronecker product of the $729$ grade blocks, each raised to its multiplicity:
--
--   $$B_a \;\cong\; \bigotimes_{\sigma \in \{0,\dots,8\}^3} \bigl(CW_6^{\otimes 4}\bigr)_\sigma^{\,\otimes \mu_\beta(m,\sigma)} .$$
--
--   This is the first regrouping step of the Davie--Stothers extraction: the address block is a product over *positions*, and one wants a product over *grade types*, because the value analysis only sees the type of each factor.  Since the address is exact, the fibre of the type map over each $\sigma$ has exactly $\mu_\beta(m,\sigma)$ elements, and the regrouping is a permutation of the tensor factors.
--
--   The statement generalises the published fixed-profile version, which is the special case where $\beta$ is the specific ten-vector of Section 5; nothing in the argument uses those numbers.
--
--   *Formalization note.* The equivalence $e : (\mathrm{Fin}\ 3 \to \mathrm{Fin}\ 9) \simeq \mathrm{Fin}\ 729$ is any cardinality equivalence; it only fixes an ordering of the factors.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 (the fourth power of the Coppersmith--Winograd tensor, its ten oriented grade classes, and the block value of an exact outer address); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_general_address_group_by_ordered_grade_types
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ) (m : ℕ) (a : MME.StothersFourth.GenExactOuterAddress base m) :
    let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
      classical
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
        (Fintype.equivFin (Fin 3 → Fin 9))
    TensorObj.Isomorphic
      (gradedAddressBlock
        (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
      (TensorObj.kronFin 729 (fun s ↦
        ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
          (e.symm s)).kronPow
            (MME.StothersFourth.genJointMultiplicity base m (e.symm s)))) := by
  sorry
