-- Prove2me | Theorems.Thm_mme_CW_fourth_power_rank_and_six_symmetry
-- name    : mme_CW_fourth_power_rank_and_six_symmetry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:59:39.764775+00:00
-- url     : https://prove2.me/theorems/7ddb4b52-2b52-4be4-95cb-8e841a64bf14
-- title:
--   Rank budget and sixfold symmetry for positive powers of the fourth CW tensor
-- statement:
--   For every field K, nonnegative integer q and positive integer N, let T be the N-th tensor power of the literal fourth Coppersmith–Winograd tensor CW_q^4. Its asymptotic rank is at most ((q+2)^4)^N, and its sixfold symmetrization is isomorphic to T^6. Both conclusions concern the actual tensor, with the existing mutual-restriction notion of isomorphism. The statement includes fourth, eighth and higher fourth-multiple powers, without a numerical value certificate.
-- source:
--   Formal consequence of the existing proved Prove2Me fourth-CW rank and sixfold-symmetry theorems, the positive tensor-power asymptotic-rank identity, sixfold-symmetrization/power compatibility, six-symmetric-to-direct tau-value bridge, and strict value-surplus exponent bridge. The sixth-root value normalization follows Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3 and Theorem 3.2, https://arxiv.org/abs/2210.10173. This reusable algebraic capstone does not assert a new numerical value certificate.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_omega
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_power_rank_and_six_symmetry
    {K : Type u} [Field K] (q N : ℕ) (hN : 0 < N) :
    tensorAsymptoticRank ((MME.StothersFourth.cwFourthObj K q).kronPow N) ≤
        (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N ∧
      TensorObj.Isomorphic
        (sixSymmetrization ((MME.StothersFourth.cwFourthObj K q).kronPow N))
        (((MME.StothersFourth.cwFourthObj K q).kronPow N).kronPow 6) := by
  sorry
