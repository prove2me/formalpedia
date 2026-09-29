-- Prove2me | Theorems.Thm_mme_omega_strassen_lt_2375477
-- name    : mme_omega_strassen_lt_2375477
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:19:20.911846+00:00
-- url     : https://prove2.me/theorems/f2d7520e-791e-4a46-bb55-da9b9f0307df
-- title:
--   Coppersmith--Winograd gives the Strassen exponent below 2.375477
-- statement:
--   Over every field $K$, the Strassen-form matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{2375477}{1000000}=2.375477.
--   $$
--
--   This is the six-decimal Coppersmith--Winograd endpoint. It combines the unchanged proved $q=6$ exact-profile tensor-square auxiliary inequality with a fully exact numerical certificate at $\tau=2375477/3000000$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8 and the printed q=6 bound on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
import Theorems.Thm_mme_CW_auxiliary_numeric_2375477
import Theorems.Thm_mme_CW_endpoint_of_numeric_certificate

open MME

universe u

theorem mme_omega_strassen_lt_2375477 {K : Type u} [Field K] :
    matMulExp_strassen K < 2375477 / 1000000 := by sorry
