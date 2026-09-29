-- Prove2me | Theorems.Thm_mme_schonhage_pan_sidePoly_coeff_zero_to_five
-- name    : mme_schonhage_pan_sidePoly_coeff_zero_to_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:19.65031+00:00
-- url     : https://prove2.me/theorems/21cec327-a2cf-4c4a-a29d-2b7422e2763b
-- title:
--   Pan side-polynomial cancellation in degrees zero through five
-- statement:
--   Fix one of the two signed halves of Pan's scalar certificate and one coordinate in each tensor mode. The resulting side polynomial has zero coefficient in every degree from zero through five. This is the low-degree cancellation block of the order-12 certificate.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_sidePoly_coeff_zero_to_five
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (s : Fin 2)
    (n : ℕ) (hn : n < 6) :
    (PanLeanBridge.sidePoly (K := K) q0 q1 q2 s).coeff n = 0 := by sorry
