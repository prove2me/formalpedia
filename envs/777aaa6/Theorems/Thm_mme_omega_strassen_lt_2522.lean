-- Prove2me | Theorems.Thm_mme_omega_strassen_lt_2522
-- name    : mme_omega_strassen_lt_2522
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:56:50.4204+00:00
-- url     : https://prove2.me/theorems/7e7f5263-5a27-4e12-b41c-57337760516a
-- title:
--   Schönhage–Pan–Winograd bound in Strassen-preorder form
-- statement:
--   For every field $K$, the matrix-multiplication exponent defined using Strassen's restriction rank satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{1261}{500}=2.522.
--   $$
--
--   This is the Strassen-preorder form of the Schönhage–Pan–Winograd bound. It is the direct analogue of the existing theorem `mme_omega_strassen_lt` in the $2.55$ mission and is the form obtained from the asymptotic sum inequality.
-- source:
--   A. Schönhage, Partial and Total Matrix Multiplication, SIAM J. Comput. 10(3), 1981, DOI 10.1137/0210032; Francesco Romani, Some Properties of Disjoint Sums of Tensors Related to Matrix Multiplication, CNR Nota Interna B80-4, February 1980, printed p. 6 (PDF p. 7).

import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_omega_strassen_lt_2522 {K : Type u} [Field K] :
    matMulExp_strassen K < 1261 / 500 := by sorry
