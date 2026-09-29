-- Prove2me | Theorems.Thm_mme_schonhage_pan_Phi_coeff_repr
-- name    : mme_schonhage_pan_Phi_coeff_repr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:01:40.073849+00:00
-- url     : https://prove2.me/theorems/3549e952-5d29-4b3d-8732-1b309c3260d7
-- title:
--   Coordinates of the Schönhage–Pan polynomial tensor family
-- statement:
--   Let $K$ be a field and let $\Phi_K(\lambda)$ be the explicit 156-slot polynomial tensor family in the Schönhage–Pan certificate. For every degree $n$ and every triple $q=(q_0,q_1,q_2)$ of basis variables, the $q$-coordinate of the degree-$n$ tensor coefficient is the degree-$n$ scalar coefficient of the corresponding certificate polynomial:
--
--   $$
--   [\Phi_K]_{n,q}=[P_{q_0,q_1,q_2}]_n.
--   $$
--
--   This identity is the coordinate bridge between the polynomial linear maps defining the degeneration and the scalar cancellation calculation.
-- source:
--   Victor Y. Pan, New combinations of methods for the acceleration of matrix multiplications, Computers & Mathematics with Applications 7 (1981), Appendix p. 125 (PDF p. 53), Tables 19.3''–19.9.

import Definitions.Def_mme_schonhage_pan_certificate
open MME PiTensorProduct BigOperators Finset Polynomial
universe u

theorem mme_schonhage_pan_Phi_coeff_repr
    {K : Type u} [Field K] (n : ℕ)
    (q : ∀ r : Fin 3, PanLeanBridge.Var r) :
    (PanLeanBridge.tensorBasis (K := K)).repr
        ((PanLeanBridge.Phi (K := K)).coeff n) q =
      (PanLeanBridge.fullPoly (K := K) (q 0) (q 1) (q 2)).coeff n := by sorry
