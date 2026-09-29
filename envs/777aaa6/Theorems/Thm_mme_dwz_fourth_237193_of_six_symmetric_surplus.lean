-- Prove2me | Theorems.Thm_mme_dwz_fourth_237193_of_six_symmetric_surplus
-- name    : mme_dwz_fourth_237193_of_six_symmetric_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:03:12.99839+00:00
-- url     : https://prove2.me/theorems/5eb85d36-7f32-4bd9-a772-1776cc0a796e
-- title:
--   A strict sixfold value surplus gives the DWZ fourth-power exponent bound
-- statement:
--   Let $K$ be any field, set $T=CW_5^{\otimes4}$ and $\tau_0=790643/1000000$, and suppose there exists an achieved six-symmetrized $\tau_0$-value $V$ strictly above the fourth-power rank budget:
--   $$
--   V>2401,\qquad V_{\tau_0}^{(6)}(T)\ge V.
--   $$
--   Then the matrix-multiplication exponent over $K$ obeys
--   $$
--   \operatorname{matMulExp}(K)<\frac{237193}{100000}=2.37193.
--   $$
--   The hypothesis is a value statement about the actual fourth CW tensor, with the sixth-root normalization of DWZ Definition 3.3. This conditional theorem supplies the final implication once the recursive construction and rigorous numerical certificate establish the strict surplus.
--
--   **Formalization Note** The value predicate is the existing HasSixSymmetricTauValueAtLeast. The proof obtains the stronger bound $\operatorname{matMulExp}(K)<3\tau_0=2.371929$ before the final exact rational comparison. The existence of the surplus remains an explicit hypothesis.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Theorem 3.2 (printed p. 16), Definition 3.3 (printed p. 18), Equation (25), and Table 3 (printed p. 78); https://arxiv.org/abs/2210.10173. Released Script.m verifies power4_dup_2.371919.mat at 2.37191840 with q=5. The rational internal parameter 790643/1000000 and endpoint 237193/100000 are conservative formalization choices; this theorem is conditional on an actual certified six-symmetrized value surplus, and does not treat numerical output as a proof.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_omega

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_237193_of_six_symmetric_surplus
    {K : Type u} [Field K]
    (hsurplus : ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5) (790643 / 1000000) V) :
    matMulExp K < 237193 / 100000 := by
  sorry
