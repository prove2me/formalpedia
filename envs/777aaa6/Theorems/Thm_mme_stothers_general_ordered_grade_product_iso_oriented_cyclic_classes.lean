-- Prove2me | Theorems.Thm_mme_stothers_general_ordered_grade_product_iso_oriented_cyclic_classes
-- name    : mme_stothers_general_ordered_grade_product_iso_oriented_cyclic_classes
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:42:50.299518+00:00
-- url     : https://prove2.me/theorems/1daaf55a-3ad9-4e3f-9e7c-73ada60155a0
-- title:
--   Ordered grade product equals the oriented cyclic class product (general profile)
-- statement:
--   **The ordered grade product, refactored through the fifteen oriented cyclic classes.**
--
--   Fix a strictly positive integral ten-class profile $\beta$ and a scale $m$.  The $729$ ordered grade triples $\sigma$ that carry a nonzero block of $CW_6^{\otimes 4}$ fall into ten cyclic classes; allowing also the swap of the first two modes splits these into fifteen *oriented* classes, with representatives $\rho_1,\dots,\rho_{15}$ and class map $t \mapsto c(t)$.
--
--   Then
--
--   $$\bigotimes_{t=1}^{15} \Bigl(\mathrm{sym}_3\bigl((CW_6^{\otimes 4})_{\rho_t}\bigr)\Bigr)^{\otimes\, \beta_{c(t)} m} \;\cong\; \bigotimes_{\sigma} \bigl(CW_6^{\otimes 4}\bigr)_\sigma^{\,\otimes \mu_\beta(m,\sigma)} ,$$
--
--   where $\mathrm{sym}_3$ is the cyclic symmetrization and $\mu_\beta(m,\sigma)$ the joint multiplicity of the profile.
--
--   Mathematically this is the observation that cyclically symmetrizing an oriented representative produces exactly the three blocks in its cyclic orbit, so the left side is a product over $15 \times 3 = 45$ addresses which is precisely the support of $\mu_\beta(m, \cdot)$, each appearing with the right exponent.  It is the step that lets the value analysis be carried out on the ten class values rather than on all $729$ grade triples.
--
--   *Formalization note.* The identity is proved in the isomorphism quotient `TensorQ`, a commutative semiring, where both sides become products of powers of the same elements and the content reduces to a reindexing of a finite product along an injection with the complementary factors trivial.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 (the fourth power of the Coppersmith--Winograd tensor, its ten oriented grade classes, and the block value of an exact outer address); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_stothers_oriented_cyclic_classes

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_general_ordered_grade_product_iso_oriented_cyclic_classes
    {K : Type u} [Field K] (base : Fin 10 → ℕ) (m : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 15 (fun t ↦
        (cyclicSymmetrization
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (MME.StothersFourth.fixedOrientedRep t))).kronPow
              (MME.StothersFourth.genProfileCount base m
                (MME.StothersFourth.fixedOrientedClass t))))
      (let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
          classical
          exact (Fintype.equivFin (Fin 3 → Fin 9)).trans (finCongr (by simp))
        TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.genJointMultiplicity base m (e.symm s)))) := by
  sorry
