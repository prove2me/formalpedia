-- Prove2me | Theorems.Thm_mme_stothers_phi116_exact_address_component_factorization
-- name    : mme_stothers_phi116_exact_address_component_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:13:11.442775+00:00
-- url     : https://prove2.me/theorems/4f7b6de2-98f6-4056-a410-c6bacc0e7fc2
-- title:
--   Exact component factorization of a phi_116 outer address
-- statement:
--   Fix an exact supported $\varphi_{116}$ outer address of length $2N$ with $\alpha+\beta=N$. Its literal address block is a restriction of the Kronecker product of four grouped powers: two copies of the coupled payload $D_6$ with exponent $\alpha$, and two copies of $\langle12,1,12\rangle$ with exponent $\beta$.
--
--   The ordering is $000,111,012,102$. This is the exact tensor-level regrouping behind the two-type outer extraction in Lemma 5.1(i).
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_exact_address_component_factorization
    {K : Type u} [Field K] {N alpha beta : ℕ}
    (hsum : alpha + beta = N)
    (address : CWQ6ExactCoupledAddress N alpha beta) :
    TensorObj.Restrict
      (TensorObj.kronFin 4 (fun r ↦
        (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
          (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
            alpha beta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K) address.1) := by
  sorry
