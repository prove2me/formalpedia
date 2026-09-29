-- Prove2me | Theorems.Thm_mme_more_asymmetry_237134_of_six_symmetric_surplus
-- name    : mme_more_asymmetry_237134_of_six_symmetric_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:59:39.045423+00:00
-- url     : https://prove2.me/theorems/e8caabd9-807e-49f9-bae3-4cb956b015e6
-- title:
--   A strict fourth-CW tensor value surplus gives the More Asymmetry exponent endpoint
-- statement:
--   For every field K, let T be the literal fourth Coppersmith–Winograd tensor CW_5^4 and tau=3952233/5000000. If an achieved six-symmetrized tau-value V of T is strictly greater than 2401, then matMulExp(K) < 237134/100000 = 2.37134. The surplus is an explicit hypothesis on the actual tensor. Establishing that surplus, including the recursive extraction and rigorous numerical certificate, remains a separate task. The exact proof first obtains the stronger bound matMulExp(K) < 3*tau = 2.3713398.
-- source:
--   Conservative rational endpoint specialization motivated by More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349, q=5 fourth-power optimization. The internal tau and endpoint are formalization choices, not a claim that a numerical certificate has already been verified. The proof is solely a specialization of the generic proved rank/value/exponent bridge for the actual fourth CW tensor. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_omega

open MME

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_237134_of_six_symmetric_surplus
    {K : Type u} [Field K]
    (hsurplus : ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5) (3952233 / 5000000) V) :
    matMulExp K < 237134 / 100000 := by
  sorry
