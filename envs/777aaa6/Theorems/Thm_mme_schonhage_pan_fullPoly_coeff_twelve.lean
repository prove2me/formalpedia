-- Prove2me | Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_twelve
-- name    : mme_schonhage_pan_fullPoly_coeff_twelve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:09.054839+00:00
-- url     : https://prove2.me/theorems/17104398-5814-4d5f-bc57-077442e5d39e
-- title:
--   The scalar Pan certificate has the prescribed degree-12 coefficient
-- statement:
--   For every field and every triple of basis-coordinate labels, the degree-12 coefficient of Pan's explicit scalar polynomial is exactly the sum, over the two signed copies, of the three desired matrix-multiplication monomials. This isolates the finite polynomial arithmetic in the leading-coefficient certificate.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open BigOperators
universe u

theorem mme_schonhage_pan_fullPoly_coeff_twelve
    {K : Type u} [Field K]
    (q0 : PanLeanBridge.Var0) (q1 : PanLeanBridge.Var1)
    (q2 : PanLeanBridge.Var2) :
    (PanLeanBridge.fullPoly (K := K) q0 q1 q2).coeff 12 =
      ∑ s : Fin 2, PanLeanBridge.targetSide (K := K) q0 q1 q2 s := by sorry
