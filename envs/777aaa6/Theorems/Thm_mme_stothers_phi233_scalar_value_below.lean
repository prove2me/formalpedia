-- Prove2me | Theorems.Thm_mme_stothers_phi233_scalar_value_below
-- name    : mme_stothers_phi233_scalar_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:26:40.931979+00:00
-- url     : https://prove2.me/theorems/7bdc8c55-1076-4410-84f2-2bb496cffa6c
-- title:
--   Exponent-independent scalar value below 192741120 for the cyclic q6 fourth-power 233 constituent
-- statement:
--   Let $K$ be a field and let $T$ be the cyclic symmetrization of the $(2,3,3)$ constituent of the fourth tensor power of the Coppersmith–Winograd tensor at $q=6$. For every real exponent $\tau$ and every $V$ with $0\le V<192741120$, one has $\operatorname{HasTauValueAtLeast}(T,\tau,V)$. The constant is the analytic profile endpoint at exponent $2/3$; the scalar-value conclusion holds at every real exponent.
-- source:
--   Scalar component bounds and the established actual-degree isolated-profile extraction for the Stothers 233 constituent.

import Definitions.Def_mme_stothers_phi233_profile_data
open MME MME.StothersFourth MME.StothersFourth.Phi233
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_scalar_value_below
    {K : Type u} [Field K] (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < 192741120) :
    HasTauValueAtLeast (cyclicSymmetrization
      (cwFourthConstituent K 6 2 3 3)) tau V := by sorry
