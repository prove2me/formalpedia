-- Prove2me | Theorems.Thm_mme_CW_2376_profile_weight_arithmetic
-- name    : mme_CW_2376_profile_weight_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:08:08.4786+00:00
-- url     : https://prove2.me/theorems/c0539e0f-b9f0-4a8e-bf40-1a73616f8096
-- title:
--   Exact weight arithmetic for the CW 2.376 profile
-- statement:
--   At scale m, suppose a nonnegative finite coupled weight W satisfies V_c^m(1-delta) <= W, with V_c >= 0 and 0 < delta < 1. Then P(tau,V_c)^(3000000m)(1-delta)^616627 is at most the tau-weight of the elementary square side 12^(75036m)38^(307638m), multiplied by W^616627. The exponents are exact: the rectangular classes contribute 225108m powers of 12, the central classes contribute 922914m powers of 38, and d times 3000000m equals 616627m.
-- source:
--   Coppersmith--Winograd (1990), exact orbit counts from equations (11)--(13) and auxiliary numerator on journal pp. 266--269.

import Definitions.Def_mme_CW_2376_profile_data
open MME

theorem mme_CW_2376_profile_weight_arithmetic
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (m : ℕ)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (W : ℝ) (hW_nonneg : 0 ≤ W)
    (hW : Vc ^ m * (1 - delta) ≤ W) :
    cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m) *
        (1 - delta) ^ (616627 : ℕ) ≤
      ((((cw2376ProfileSide m * cw2376ProfileSide m *
          cw2376ProfileSide m : ℕ) : ℝ) ^ tau) *
        W ^ (616627 : ℕ)) := by
  sorry
