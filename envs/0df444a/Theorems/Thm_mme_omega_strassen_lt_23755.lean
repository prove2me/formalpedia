-- Prove2me | Theorems.Thm_mme_omega_strassen_lt_23755
-- name    : mme_omega_strassen_lt_23755
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:16:31.421774+00:00
-- url     : https://prove2.me/theorems/ff9c8c76-112e-4609-9500-edcbf0a7e370
-- title:
--   Coppersmith--Winograd gives the Strassen exponent below 2.3755
-- statement:
--   Over every field $K$, the Strassen-form matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{4751}{2000}=2.3755.
--   $$
--
--   The bound uses the proved $q=6$ Coppersmith--Winograd tensor-square auxiliary inequality at the exact CW90 profile, together with its exact strict numerical certificate at $\tau=4751/6000$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8 and the q=6 endpoint on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
import Theorems.Thm_mme_CW_auxiliary_numeric_23755
import Theorems.Thm_mme_CW_endpoint_of_numeric_certificate

open MME

universe u

theorem mme_omega_strassen_lt_23755 {K : Type u} [Field K] :
    matMulExp_strassen K < 4751 / 2000 := by sorry
