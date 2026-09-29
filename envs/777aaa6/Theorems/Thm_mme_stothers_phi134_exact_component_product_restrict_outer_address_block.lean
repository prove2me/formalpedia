-- Prove2me | Theorems.Thm_mme_stothers_phi134_exact_component_product_restrict_outer_address_block
-- name    : mme_stothers_phi134_exact_component_product_restrict_outer_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:45:15.626437+00:00
-- url     : https://prove2.me/theorems/0bee3994-d063-4c3f-8db2-83c886da0420
-- title:
--   The eight phi_134 component powers restrict every exact outer address block
-- statement:
--   Let $x$ be an exact $\\Phi_{1,3,4}$ profile with fine-label multiplicities
--
--   $$
--   (\\alpha,\\beta,\\gamma,\\delta,\\delta,\\gamma,\\beta,\\alpha).
--   $$
--
--   The ordered product of the eight algebraic component tensors raised to these multiplicities restricts the literal graded-address block $B(x)$ inside $\\Phi_{1,3,4}^{\\otimes 2N}$. This is the complete tensor-algebra interface used after the hashing step: each retained address carries the correct product of rectangular and coupled components.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), printed p. 365, including the eight component factors and their exact profile multiplicities; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_stothers_phi134_outer_grading

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_exact_component_product_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 8 (fun r ↦
        (MME.StothersFourth.Phi134.componentObj K q r).kronPow
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi134.outerGrading K q) address.1.1) := by
  sorry
