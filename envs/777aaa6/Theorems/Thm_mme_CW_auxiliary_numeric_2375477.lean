-- Prove2me | Theorems.Thm_mme_CW_auxiliary_numeric_2375477
-- name    : mme_CW_auxiliary_numeric_2375477
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:16:54.383211+00:00
-- url     : https://prove2.me/theorems/45b05bff-a31b-489b-8faf-b2890c680dbc
-- title:
--   Exact CW numerical certificate at the printed 2.375477 endpoint
-- statement:
--   For the exact normalized Coppersmith--Winograd profile used in the proved $q=6$ tensor-square analysis, the auxiliary expression at $\tau=2375477/3000000$ satisfies
--
--   $$
--   64 < A\!\left(\frac{2375477}{3000000}\right).
--   $$
--
--   Because $3\tau=2375477/1000000=2.375477$, this certifies the six-decimal endpoint printed by Coppersmith and Winograd while reusing the existing tensor extraction unchanged.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8 auxiliary equation and printed q=6 bound on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_mme_CW_auxiliary_RHS

open MME

theorem mme_CW_auxiliary_numeric_2375477 :
    (64 : ℝ) <
      auxiliaryRHS 6 (2375477 / 3000000)
        cw2376_a cw2376_b cw2376_c cw2376_d := by sorry
