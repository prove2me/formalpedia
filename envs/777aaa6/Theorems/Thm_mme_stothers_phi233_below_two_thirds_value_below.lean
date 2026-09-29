-- Prove2me | Theorems.Thm_mme_stothers_phi233_below_two_thirds_value_below
-- name    : mme_stothers_phi233_below_two_thirds_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:27:58.594984+00:00
-- url     : https://prove2.me/theorems/962c2ce8-155f-419e-b8ec-e6979a2429c5
-- title:
--   Analytic value bound below two thirds for the cyclic q6 fourth-power 233 constituent
-- statement:
--   Let $K$ be a field and let $T$ be the cyclic symmetrization of the $(2,3,3)$ constituent of the fourth tensor power of the Coppersmith–Winograd tensor at $q=6$. For every real exponent $\tau$ with $3\tau\le2$ and every $V$ with $0\le V<\operatorname{classValue}(6,\tau,9)$, one has $\operatorname{HasTauValueAtLeast}(T,\tau,V)$. Thus the analytic value estimate for this constituent holds throughout the lower exponent range, including negative exponents.
-- source:
--   The exponent-independent scalar endpoint bound and an analytic comparison with the endpoint at two thirds.

import Definitions.Def_mme_stothers_phi233_profile_data
open MME MME.StothersFourth MME.StothersFourth.Phi233
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_below_two_thirds_value_below
    {K : Type u} [Field K] (tau V : ℝ) (htau : 3 * tau ≤ 2)
    (hV : 0 ≤ V) (hVlt : V < classValue 6 tau 9) :
    HasTauValueAtLeast (cyclicSymmetrization
      (cwFourthConstituent K 6 2 3 3)) tau V := by sorry
