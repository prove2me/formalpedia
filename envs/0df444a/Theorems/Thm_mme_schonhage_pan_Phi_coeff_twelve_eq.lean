-- Prove2me | Theorems.Thm_mme_schonhage_pan_Phi_coeff_twelve_eq
-- name    : mme_schonhage_pan_Phi_coeff_twelve_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T03:54:19.374601+00:00
-- url     : https://prove2.me/theorems/0dc3aedc-a448-4f5e-9bed-a9783d9dbd39
-- title:
--   The order-12 Pan coefficient is the triple matrix tensor
-- statement:
--   For every field $K$, the degree-12 coefficient of the explicit 156-slot Schönhage–Pan polynomial tensor family $\Phi_K$ equals the tensor of $\langle1,5,22\rangle \oplus \langle11,2,5\rangle \oplus \langle10,11,1\rangle$. This is the leading-coefficient half of the characteristic-free order-12 degeneration certificate.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME
universe u

theorem mme_schonhage_pan_Phi_coeff_twelve_eq
    {K : Type u} [Field K] :
    (PanLeanBridge.Phi (K := K)).coeff 12 =
      (PanLeanBridge.Xobj (K := K)).t := by sorry
