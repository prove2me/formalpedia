-- Prove2me | Theorems.Thm_mme_omega_lt_2522_of_sum_le
-- name    : mme_omega_lt_2522_of_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-23T22:56:39.217162+00:00
-- url     : https://prove2.me/theorems/c64deb47-f7f1-4f17-a80b-bb6b683fecf3
-- title:
--   Exact numerical endpoint for the 110–156 sum inequality
-- statement:
--   Let $K$ be any field and let $\omega_K^{\mathrm{Str}}$ denote the matrix-multiplication exponent defined using Strassen's restriction rank. If
--
--   $$
--   3\cdot110^{\omega_K^{\mathrm{Str}}/3}\le156,
--   $$
--
--   then
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{1261}{500}=2.522.
--   $$
--
--   This is the exact numerical endpoint used by the $n=11$, $k=5$ construction. The endpoint comparison can be certified without floating point by reducing it to the natural-number inequality $52^{1500}<110^{1261}$.
-- source:
--   Numerical consequence of the n=11, k=5 Pan–Winograd construction reported in Francesco Romani, CNR Nota Interna B80-4, February 1980, printed p. 6 (PDF p. 7), and of Schönhage's bound 3 log(52)/log(110).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_omega_strassen
universe u
open MME

theorem mme_omega_lt_2522_of_sum_le {K : Type u} [Field K]
    (h : 3 * (110 : ℝ) ^ (matMulExp_strassen K / 3) ≤ 156) :
    matMulExp_strassen K < 1261 / 500 := by sorry
