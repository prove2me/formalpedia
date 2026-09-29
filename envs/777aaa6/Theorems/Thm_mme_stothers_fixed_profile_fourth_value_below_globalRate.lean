-- Prove2me | Theorems.Thm_mme_stothers_fixed_profile_fourth_value_below_globalRate
-- name    : mme_stothers_fixed_profile_fourth_value_below_globalRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:23:45.386004+00:00
-- url     : https://prove2.me/theorems/23294a99-31ee-4f8d-ac6b-343b22f3f63a
-- title:
--   Fixed-profile Stothers fourth-power value below the global rate
-- statement:
--   Let $K$ be any field. Fix
--   $$
--   \tau_0=\frac{23737}{30000}
--   $$
--   and the exact ten-class profile
--   $$
--   b=\frac{1}{97{,}942{,}072}
--   (98,1862,73075,1023050,3626000,98000,2156000,13720000,21560000,38710000).
--   $$
--   For every real $V\ge 0$ satisfying
--   $$
--   V<\operatorname{globalRate}(6,\tau_0,b,b),
--   $$
--   the literal fourth Coppersmith--Winograd object obeys
--   $$
--   \operatorname{HasTauValueAtLeast}
--   \bigl(CW_6^{\otimes4},\tau_0,V\bigr).
--   $$
--   This is the exact fixed-profile specialization of the fourth-power extraction needed for the $2.3737$ endpoint. The strict inequality records the limiting exponential rate without asserting attainment of the limiting base itself. The profile is an exact nearby stationary witness and is not asserted to equal the unrounded optimizer behind the decimals in Table 2.
--
--   **Formalization Note** The object is the mission's literal fourth tensor power cwFourthObj; the statement does not replace its interacting blocks by an external direct sum.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Theorem 5.3, Equation (5.3), and Table 2, printed pp. 367–368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf; DOI 10.1017/S0308210511001646. The exact rational profile is the audited nearby stationary witness in Definitions.Def_mme_stothers_fixed_outer_profile.

import Definitions.Def_mme_stothers_fixed_outer_profile

open MME

universe u

theorem mme_stothers_fixed_profile_fourth_value_below_globalRate
    {K : Type u} [Field K] :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 (23737 / 30000)
        MME.StothersFourth.fixedProfileB
        MME.StothersFourth.fixedProfileB →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6)
        (23737 / 30000) V := by
  sorry
