-- Prove2me | Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_ten_zero
-- name    : mme_schonhage_pan_fullPoly_coeff_ten_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:29.759156+00:00
-- url     : https://prove2.me/theorems/fcc079a1-ae45-434a-98ec-870f2ce8b8ba
-- title:
--   Pan's signed scalar certificate cancels in degree ten
-- statement:
--   For every coordinate triple, the degree-ten coefficient of the sum of Pan's two signed side polynomials is zero. Each side contributes the same residual contraction with opposite sign, so the two sides cancel over every field.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_fullPoly_coeff_ten_zero
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff 10 = 0 := by sorry
