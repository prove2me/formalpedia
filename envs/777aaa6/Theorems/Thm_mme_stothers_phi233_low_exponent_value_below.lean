-- Prove2me | Theorems.Thm_mme_stothers_phi233_low_exponent_value_below
-- name    : mme_stothers_phi233_low_exponent_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T08:07:43.059801+00:00
-- url     : https://prove2.me/theorems/5e1215c2-3ef7-4fec-bbd7-bf6aa79461d1
-- title:
--   The Stothers phi233 value bound for exponents at most one third
-- statement:
--   Let $K$ be any field and let $\tau,V$ be real numbers with $3\tau\le1$ and $0\le V<\operatorname{classValue}(6,\tau,9)$. Then the cyclic symmetrization of the fourth-power Coppersmith–Winograd constituent $\phi_{233}$ at $q=6$ has $\tau$-value at least $V$.
--
--   This establishes the low-exponent case of the unrestricted $\phi_{233}$ value claim. The hypotheses allow negative exponents. The proof extracts a square matrix tensor of side $1296$ and uses scalar blocks, whose weights are one for every real exponent.
-- source:
--   Stothers fourth-power constituent phi233: scalar extraction from a high-high fine block.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value
open MME MME.StothersFourth
universe u
set_option autoImplicit false

theorem mme_stothers_phi233_low_exponent_value_below
    {K : Type u} [Field K] (tau V : ℝ) (htau : 3 * tau ≤ 1)
    (hV : 0 ≤ V) (hVlt : V < classValue 6 tau 9) :
    HasTauValueAtLeast (cyclicSymmetrization
      (cwFourthConstituent K 6 2 3 3)) tau V := by sorry
