-- Prove2me | Theorems.Thm_mme_stothers_phi116_profile_extraction_of_exact_address_factorization
-- name    : mme_stothers_phi116_profile_extraction_of_exact_address_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:36:05.346718+00:00
-- url     : https://prove2.me/theorems/1e0257d5-7b3f-409e-8221-b114c8f66aaa
-- title:
--   Phi_116 finite four-edge extraction at a legal profile
-- statement:
--   Fix a legal recursive frequency $0<a<1$ and assume the exact tensor factorization for every supported $\varphi_{116}$ address of profile $(\alpha,\beta)$. If $2\le 3\tau\le3$, then every nonnegative value strictly below the associated two-type rate is attained by the cyclically symmetrized literal constituent: $$V<4\left(\frac{2L}{a}\right)^a\left(\frac{E^2}{1-a}\right)^{1-a} \Longrightarrow V_\tau(\operatorname{cyc}(\varphi_{116}))\ge V,$$ where $E=12^{3\tau}$ and $L=4\,6^{3\tau}(6^{3\tau}+2)$. This is exactly the remaining finite type selection, four-edge Salem--Spencer pruning, loss absorption, and cofinal-limit step after literal address factorization; continuous optimization is deliberately separated.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_profile_extraction_of_exact_address_factorization
    {K : Type u} [Field K] (tau a : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (haPos : 0 < a) (haLt : a < 1)
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
      V < 4 *
        (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
          ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
            (1 - a)) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  sorry
