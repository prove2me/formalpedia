-- Prove2me | Theorems.Thm_mme_dwz_fourth_fixed_tau_value_surplus
-- name    : mme_dwz_fourth_fixed_tau_value_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T15:50:39.034877+00:00
-- url     : https://prove2.me/theorems/63bb193b-fa36-44f2-b9a2-b664e6172ea8
-- title:
--   DWZ fourth-power strict value surplus above 2401
-- statement:
--   For every field $K$, let $T=CW_5^{\otimes4}$ be the literal fourth tensor power and let $\tau=790643/1000000$. There exists a real number $V$ such that
--
--   $$2401<V\quad\text{and}\quad V_{\tau}^{(6)}(T)\ge V.$$
--
--   The bound $2401=7^4$ is the fourth-power asymptotic-rank budget. The six-symmetrized value uses the sixth-root normalization of DWZ Definition 3.3 and is represented by cofinal finite extractions into direct sums of actual matrix-multiplication tensors. The strict surplus is the substantive fourth-power target supplied by the recursive restricted-value construction and exact numerical certificate; it is not an assumed property of a certificate record.
--
--   The released fourth-power witness is checked numerically at exponent 2.37191840. This target uses the larger internal exponent $3\tau=2.371929$, leaving room for exact rationalization and directed bounds before the final endpoint $2.37193$. The formal statement asserts the exact surplus, not correctness of the floating-point verifier.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Definition 3.3 (printed p. 18), Equation (25) (p. 58), Equation (34) (p. 71), Section 8.3 and Table 3 (pp. 77–78), https://arxiv.org/abs/2210.10173. Released code https://osf.io/dta6p/, src/Script.m: LoadAndVerify('../data/power4_dup_2.371919.mat', 2.37191840, true), with q=5 and fourth power. The new rational tau is an upward relaxation of that witness endpoint.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_fixed_tau_value_surplus
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        (790643 / 1000000) V := by
  sorry
