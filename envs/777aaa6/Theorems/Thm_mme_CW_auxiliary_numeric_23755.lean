-- Prove2me | Theorems.Thm_mme_CW_auxiliary_numeric_23755
-- name    : mme_CW_auxiliary_numeric_23755
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:10:09.131929+00:00
-- url     : https://prove2.me/theorems/d2eca661-7181-4b1a-9436-828dffdf50f5
-- title:
--   Exact CW numerical certificate at exponent 2.3755
-- statement:
--   For the exact normalized Coppersmith--Winograd profile used in the proved $q=6$ tensor-square analysis, the auxiliary expression at $\tau=4751/6000$ satisfies
--
--   $$
--   64 < A\!\left(\frac{4751}{6000}\right).
--   $$
--
--   Since $3\tau=4751/2000=2.3755$, this is the strict numerical certificate needed to sharpen the existing $\omega<2.376$ endpoint without changing its tensor extraction or profile.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8 auxiliary equation and q=6 parameter choice on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_mme_CW_auxiliary_RHS

open MME

theorem mme_CW_auxiliary_numeric_23755 :
    (64 : ℝ) <
      auxiliaryRHS 6 (4751 / 6000)
        cw2376_a cw2376_b cw2376_c cw2376_d := by sorry
