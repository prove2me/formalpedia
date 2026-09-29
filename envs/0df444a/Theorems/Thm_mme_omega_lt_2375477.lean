-- Prove2me | Theorems.Thm_mme_omega_lt_2375477
-- name    : mme_omega_lt_2375477
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:20:53.955505+00:00
-- url     : https://prove2.me/theorems/b04f7ea3-a79c-41f5-a92c-371072e66829
-- title:
--   Coppersmith--Winograd bound: omega below 2.375477
-- statement:
--   For every field $K$, the matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K<\frac{2375477}{1000000}=2.375477.
--   $$
--
--   This is the printed six-decimal Coppersmith--Winograd bound, formalized with the same theorem shape and exponent definition as the existing $\omega_K<2.376$ mission.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), printed bound on journal p. 269; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_2375477

open MME

universe u

theorem mme_omega_lt_2375477 {K : Type u} [Field K] :
    matMulExp K < 2375477 / 1000000 := by sorry
