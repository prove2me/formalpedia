-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization
-- name    : mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:13:27.950566+00:00
-- url     : https://prove2.me/theorems/da111561-58c5-4a8f-8b13-369753078cc2
-- title:
--   Phi_116 hashing and value after exact address factorization
-- statement:
--   Assume the exact tensor factorization for every supported $\varphi_{116}$ address of profile $(\alpha,\beta)$: each literal address block is reached from two coupled powers of multiplicity $\alpha$ and two rectangular powers of multiplicity $\beta$. If $2\le3\tau\le3$, prove every nonnegative value strictly below the Davie--Stothers class-$116$ endpoint.
--
--   This isolates the remaining value-facing argument in Lemma 5.1(i): outer Salem--Spencer extraction, strict-below coupled values, optimal-profile approximation, loss absorption, and the cofinal limit. Literal support, component identification, exact counts, and tensor regrouping are supplied by the hypothesis.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hfactor :
      ∀ {N alpha beta : ℕ}, alpha + beta = N →
        ∀ address : CWQ6ExactCoupledAddress N alpha beta,
          TensorObj.Restrict
            (TensorObj.kronFin 4 (fun r ↦
              (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
                (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
                  alpha beta r)))
            (gradedAddressBlock
              (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K)
              address.1)) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  sorry
