-- Prove2me | Theorems.Thm_mme_more_asymmetry_fourth_fixed_tau_value_surplus
-- name    : mme_more_asymmetry_fourth_fixed_tau_value_surplus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-05T16:32:50.517715+00:00
-- url     : https://prove2.me/theorems/dc4a685e-8b0c-42bf-8cc6-aa54d48b50fc
-- title:
--   More Asymmetry: strict fourth-power value surplus at tau = 3952233/5000000
-- statement:
--   For every field $K$, let $T=CW_5^{\otimes4}$ be the literal fourth tensor power and let $\tau_0=3952233/5000000$. There is a real $V>2401$ such that $T$ has six-symmetrized $\tau_0$-value at least $V$ in the existing finite-witness semantics.
--
--   Concretely, the sixfold symmetrization admits, at arbitrarily large powers and every positive relative tolerance, restrictions to finite direct sums of actual matrix-multiplication tensors with total tau-weight at least the corresponding power of $V^6$ times one minus that tolerance. This is a genuine tensor-value conclusion, not a certificate record assuming its own soundness.
--
--   The target must be proved by the complete-split, six-region, sequential-ownership and hole-repair construction together with exact numerical certification. The internal exponent $3\tau_0=2.3713398$ is above the source's 2.371339 bound and below the mission's 2.37134 endpoint. Neither the supplied floating-point verifier nor an unproved DWZ surplus is a premise.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, SODA 2025, arXiv:2404.16349v2; Section 7, pp.40–41, Table1,p.2; https://arxiv.org/abs/2404.16349v2. q=5, fourth power, original bound 2.371339. OSF https://osf.io/mw5ak/, original code_matrix_mult.zip SHA256 a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8; data/W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Floating-point verifier is not an exact Lean certificate. The source-level construction is Theorems5.3,6.2,6.4 and Equation(7).

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

universe u
open MME
set_option autoImplicit false

theorem mme_more_asymmetry_fourth_fixed_tau_value_surplus
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5) (3952233 / 5000000) V := by sorry
