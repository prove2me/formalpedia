-- Prove2me | Theorems.Thm_mme_stothers_phi116_exact_address_factor_exponents
-- name    : mme_stothers_phi116_exact_address_factor_exponents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:13:03.393484+00:00
-- url     : https://prove2.me/theorems/f1fd4236-da75-46d1-ae87-f379e31e85a4
-- title:
--   Exact recursive and rectangular exponents for phi_116
-- statement:
--   In an exact $\varphi_{116}$ outer address with $\alpha+\beta=N$, the two recursive types occur $2\alpha$ times in total and the two rectangular types occur $2\beta$ times. After cyclic symmetrization each rectangular factor contributes two side-$12$ directions, giving the source-correct side exponent $4\beta$.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data

open MME

set_option autoImplicit false

theorem mme_stothers_phi116_exact_address_factor_exponents
    {N alpha beta : ℕ} (hsum : alpha + beta = N)
    (address : MME.CWQ6ExactCoupledAddress N alpha beta) :
    let recursiveCount :=
      ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦
        MME.StothersFourth.Phi116.phi116OuterComponent address.1 j = 0 ∨
          MME.StothersFourth.Phi116.phi116OuterComponent address.1 j = 1)).card
    let rectangularCount :=
      ((Finset.univ : Finset (Fin (2 * N))).filter (fun j ↦
        MME.StothersFourth.Phi116.phi116OuterComponent address.1 j = 2 ∨
          MME.StothersFourth.Phi116.phi116OuterComponent address.1 j = 3)).card
    recursiveCount = 2 * alpha ∧
      rectangularCount = 2 * beta ∧
      2 * rectangularCount = 4 * beta := by
  sorry
