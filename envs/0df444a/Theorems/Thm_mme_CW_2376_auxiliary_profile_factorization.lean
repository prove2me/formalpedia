-- Prove2me | Theorems.Thm_mme_CW_2376_auxiliary_profile_factorization
-- name    : mme_CW_2376_auxiliary_profile_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:55:53.360253+00:00
-- url     : https://prove2.me/theorems/0f7761e3-db9b-4daa-8154-5b2b8dd65ccc
-- title:
--   Factor the generalized CW auxiliary base
-- statement:
--   At the exact rational $q=6$ profile, the generalized Section 8 base factors as $$B_{V_c}(6,\tau,a,b,c,d)=H P(\tau,V_c),$$ where $H$ is the reciprocal five-marginal entropy denominator and $P$ is the product of the six rectangular, three central, and free coupled constituent bases. This separates survivor counting from constituent substitution.
-- source:
--   Coppersmith--Winograd (1990), equation (13) and the auxiliary equation on journal pp. 268--269.

import Definitions.Def_mme_CW_2376_profile_data
open MME

theorem mme_CW_2376_auxiliary_profile_factorization
    (tau Vc : ℝ) :
    auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d Vc =
      cw2376ProfileCountBase *
        cw2376ProfileNumeratorBase tau Vc := by
  sorry
