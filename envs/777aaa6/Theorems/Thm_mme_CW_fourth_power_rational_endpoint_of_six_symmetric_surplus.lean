-- Prove2me | Theorems.Thm_mme_CW_fourth_power_rational_endpoint_of_six_symmetric_surplus
-- name    : mme_CW_fourth_power_rational_endpoint_of_six_symmetric_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T17:17:34.921705+00:00
-- url     : https://prove2.me/theorems/a6993ed4-1854-406b-91b5-b55f100d5d1b
-- title:
--   A strict value surplus for a positive fourth-CW power implies a rational exponent endpoint
-- statement:
--   For every field K, nonnegative integer q, positive integer N, positive real tau and rational b with 3*tau <= b, suppose an achieved six-symmetrized tau-value V of (CW_q^4)^N is strictly greater than ((q+2)^4)^N. Then matMulExp(K) < b. In particular the q=5,N=2 source has rank budget 5764801, not 2401. The numerical value surplus remains an explicit hypothesis; no endpoint or numerical optimizer output is assumed as a theorem.
-- source:
--   Formal consequence of the existing proved Prove2Me fourth-CW rank and sixfold-symmetry theorems, the positive tensor-power asymptotic-rank identity, sixfold-symmetrization/power compatibility, six-symmetric-to-direct tau-value bridge, and strict value-surplus exponent bridge. The sixth-root value normalization follows Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3 and Theorem 3.2, https://arxiv.org/abs/2210.10173. This reusable algebraic capstone does not assert a new numerical value certificate.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_omega
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_power_rational_endpoint_of_six_symmetric_surplus
    {K : Type u} [Field K] (q N : ℕ) (hN : 0 < N)
    (tau : ℝ) (bound : ℚ)
    (htau : 0 < tau) (hbound : 3 * tau ≤ (bound : ℝ))
    (hsurplus : ∃ V : ℝ, (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N < V ∧
      HasSixSymmetricTauValueAtLeast
        ((MME.StothersFourth.cwFourthObj K q).kronPow N) tau V) :
    matMulExp K < (bound : ℝ) := by
  sorry
