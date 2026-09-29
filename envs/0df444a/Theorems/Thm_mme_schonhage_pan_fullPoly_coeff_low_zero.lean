-- Prove2me | Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_low_zero
-- name    : mme_schonhage_pan_fullPoly_coeff_low_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T03:58:20.271249+00:00
-- url     : https://prove2.me/theorems/7e105b46-484e-4228-97da-f63f8c7cd298
-- title:
--   Pan's scalar certificate cancels below degree 12
-- statement:
--   For every choice of one coordinate in each mode, all coefficients in degrees 0 through 11 of Pan's explicit scalar certificate polynomial vanish. This isolates the finite polynomial cancellation underlying the tensor-valued statement that the Pan family has valuation at least 12.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_fullPoly_coeff_low_zero
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) (n : ℕ) (hn : n < 12) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff n = 0 := by sorry
