-- Prove2me | Theorems.Thm_mme_schonhage_pan_sidePoly_coeff_six_to_nine
-- name    : mme_schonhage_pan_sidePoly_coeff_six_to_nine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:24.717392+00:00
-- url     : https://prove2.me/theorems/421d2367-8501-413e-9820-13fd45d10ed8
-- title:
--   Pan side-polynomial cancellation in degrees six through nine
-- statement:
--   Fix one of the two signed halves of Pan's scalar certificate and one coordinate in each tensor mode. The resulting side polynomial has zero coefficient in degrees six, seven, eight, and nine. These are the nontrivial within-side cancellations among Pan's six rank-one summand families.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_sidePoly_coeff_six_to_nine
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (s : Fin 2)
    (n : ℕ) (hn6 : 6 ≤ n) (hn10 : n < 10) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff n = 0 := by sorry
