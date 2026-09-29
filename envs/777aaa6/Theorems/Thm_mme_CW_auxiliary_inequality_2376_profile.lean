-- Prove2me | Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
-- name    : mme_CW_auxiliary_inequality_2376_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:52:01.347721+00:00
-- url     : https://prove2.me/theorems/1cc67894-f0b6-438c-aec6-ce87482a1501
-- title:
--   CW auxiliary inequality at the exact 2.376 profile
-- statement:
--   Let $K$ be a field and write $\omega_K$ for its matrix-multiplication exponent in Strassen form. Assume $\omega_K\ge2$. At $q=6$ and the exact normalized Coppersmith--Winograd frequencies
--
--   $$
--   a=\frac{233}{10^6},\qquad b=\frac{12506}{10^6},\qquad c=\frac{102546}{10^6},\qquad d=\frac{616627}{3\cdot10^6},
--   $$
--
--   the Section-8 auxiliary value satisfies
--
--   $$
--   \operatorname{auxiliaryRHS}\!\left(6,\frac{\omega_K}{3},a,b,c,d\right)\le64.
--   $$
--
--   This is the exact-profile specialization of the auxiliary inequality obtained by applying the tensor-square laser extraction and the asymptotic sum inequality to the $q=6$ Coppersmith--Winograd tensor. The rational value of $d$ makes $3a+6b+3c+3d=1$ exact.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (11)–(13), auxiliary equation, and q=6 parameter choice on journal pp. 265–269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_omega_strassen
open MME
universe u

theorem mme_CW_auxiliary_inequality_2376_profile
    {K : Type u} [Field K]
    (homega : 2 ≤ matMulExp_strassen K) :
    auxiliaryRHS 6 (matMulExp_strassen K / 3)
        cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64 := by sorry
