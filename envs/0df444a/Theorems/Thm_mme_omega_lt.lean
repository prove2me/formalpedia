-- Prove2me | Theorems.Thm_mme_omega_lt
-- name    : mme_omega_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T03:36:25.996891+00:00
-- url     : https://prove2.me/theorems/39dac148-503f-449a-8e36-f0b320e2be36
-- statement:
--   **Schönhage's bound: $\omega < 2.55$.**
--
--   The matrix-multiplication exponent $\omega$ governs the asymptotic cost of multiplying $n\times n$ matrices: it is the infimum of exponents $\tau$ for which $O(n^\tau)$ arithmetic operations suffice. Equivalently (the form used here) it is the tensor-rank exponent
--
--   $$\omega = \inf_{n\ge 2} \frac{\log R(\langle n,n,n\rangle)}{\log n},$$
--
--   where $\langle n,n,n\rangle = \sum_{i,j,k} e_{ij}\otimes e_{jk}\otimes e_{ki}$ is the matrix-multiplication tensor and $R$ is tensor rank. This theorem asserts $\omega < 51/20 = 2.55$, the bound Schönhage obtained in 1981 via his $\tau$ (direct-sum) theorem and the asymptotic sum inequality. Here `matMulExp` is the tensor-rank exponent from definition `mme_omega`.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Definitions.Def_mme_omega
universe u
open MME

theorem mme_omega_lt {K : Type u} [Field K] : matMulExp K < 51 / 20 := by sorry
