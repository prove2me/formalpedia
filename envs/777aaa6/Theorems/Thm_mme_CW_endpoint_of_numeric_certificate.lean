-- Prove2me | Theorems.Thm_mme_CW_endpoint_of_numeric_certificate
-- name    : mme_CW_endpoint_of_numeric_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T07:59:12.968138+00:00
-- url     : https://prove2.me/theorems/0bc941e4-1646-4946-a714-2632221d235f
-- title:
--   A strict CW numerical certificate gives a strict exponent bound
-- statement:
--   Fix the exact normalized Coppersmith--Winograd profile used for the $q=6$ tensor-square analysis, and write $A(\tau)$ for its auxiliary expression. Let $c$ be a candidate exponent and let $w$ be any exponent parameter. If
--
--   $$
--   64<A(c/3)
--   \qquad\text{and}\qquad
--   A(w/3)\le 64,
--   $$
--
--   then $w<c$.
--
--   This theorem is the reusable endpoint interface between the source-derived tensor inequality and an exact numerical certificate. It allows any sharper certified value of $c$ at the same CW profile to improve the exponent without repeating the tensor extraction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), normalized auxiliary equation on journal p. 269 (PDF p. 19), together with monotonicity in the exponent parameter; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_mme_CW_auxiliary_RHS
import Theorems.Thm_mme_CW_auxiliary_mono

open MME

theorem mme_CW_endpoint_of_numeric_certificate
    (c w : ℝ)
    (hnumeric :
      (64 : ℝ) <
        auxiliaryRHS 6 (c / 3) cw2376_a cw2376_b cw2376_c cw2376_d)
    (haux :
      auxiliaryRHS 6 (w / 3) cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64) :
    w < c := by sorry
