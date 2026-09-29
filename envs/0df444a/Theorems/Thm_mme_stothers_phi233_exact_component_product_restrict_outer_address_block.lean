-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_component_product_restrict_outer_address_block
-- name    : mme_stothers_phi233_exact_component_product_restrict_outer_address_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:23:12.01415+00:00
-- url     : https://prove2.me/theorems/faf58c79-ea87-45cd-99d4-cbee41891774
-- title:
--   The ten phi_233 component powers restrict every exact outer address block
-- statement:
--   Let $x$ be an exact $\varphi_{233}$ profile with fine-label multiplicities
--
--   $$
--   (\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).
--   $$
--
--   The ordered product of the ten algebraic component tensors raised to these multiplicities restricts the literal graded-address block $B(x)$ inside $\varphi_{233}^{\otimes 2N}$. This is the complete tensor-algebra interface used after the hashing step: each retained address carries the correct product of rectangular and coupled components.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, including the ten component factors and their exact profile multiplicities; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi233_exact_label
import Theorems.Thm_mme_stothers_phi233_exact_profile_fine_factorization
import Theorems.Thm_mme_stothers_phi233_exact_fine_word_restrict_outer_address_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_component_product_restrict_outer_address_block
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 10 (fun r ↦
        (MME.StothersFourth.Phi233.componentObj K q r).kronPow
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi233.outerGrading K q) address.1.1) := by
  sorry
