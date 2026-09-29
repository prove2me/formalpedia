-- Prove2me | Theorems.Thm_mme_omega_lt_23755
-- name    : mme_omega_lt_23755
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:19:01.561184+00:00
-- url     : https://prove2.me/theorems/38945b93-0ecf-4e90-8666-4b41d4d09a59
-- title:
--   Coppersmith--Winograd bound: omega below 2.3755
-- statement:
--   For every field $K$, the matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K<\frac{4751}{2000}=2.3755.
--   $$
--
--   This sharpens the formalized $\omega_K<2.376$ Coppersmith--Winograd result using the same $q=6$ tensor, exact profile, and structural laser argument; only the rigorous numerical endpoint is strengthened.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), Section 8 and the q=6 endpoint on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_23755

open MME

universe u

theorem mme_omega_lt_23755 {K : Type u} [Field K] :
    matMulExp K < 4751 / 2000 := by sorry
