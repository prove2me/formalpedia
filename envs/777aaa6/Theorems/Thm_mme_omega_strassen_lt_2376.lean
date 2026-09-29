-- Prove2me | Theorems.Thm_mme_omega_strassen_lt_2376
-- name    : mme_omega_strassen_lt_2376
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T00:35:13.139988+00:00
-- url     : https://prove2.me/theorems/f4626e29-81a7-4d5f-baea-093608639890
-- title:
--   Coppersmith--Winograd bound in Strassen-preorder form
-- statement:
--   For every field $K$, the matrix-multiplication exponent defined through Strassen's restriction rank satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{297}{125}=2.376.
--   $$
--
--   This is the form produced by the Coppersmith--Winograd tensor analysis and Schonhage's asymptotic sum inequality, before transferring to the platform's tensor-rank definition of $\omega$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 269 (PDF p. 19), concluding bound omega < 2.375477; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_omega_strassen_lt_2376 {K : Type u} [Field K] :
    matMulExp_strassen K < 297 / 125 := by sorry
