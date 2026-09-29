-- Prove2me | Theorems.Thm_mme_omega_lt_237134
-- name    : mme_omega_lt_237134
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:32:38.144842+00:00
-- url     : https://prove2.me/theorems/419e7657-e652-4dfb-828f-e7f6fa7c1cd6
-- title:
--   More Asymmetry bound: omega < 2.37134
-- statement:
--   For every field $K$, the existing matrix-multiplication exponent satisfies
--
--   $$\operatorname{matMulExp}(K)<\frac{237134}{100000}=2.37134.$$
--
--   This is the original More Asymmetry fourth-power bound rounded upward from 2.371339. The statement has exactly the field quantification and exponent definition of the existing Schönhage goal. There are no characteristic, distribution, optimizer, or tensor-value hypotheses.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, SODA 2025, arXiv:2404.16349v2; Section 7, pp.40–41, Table1,p.2; https://arxiv.org/abs/2404.16349v2. q=5, fourth power, original bound 2.371339. OSF https://osf.io/mw5ak/, original code_matrix_mult.zip SHA256 a88d211df0a82f0bba0a77ccbad9103064ebef08eea95613e5926a4f666260d8; data/W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Floating-point verifier is not an exact Lean certificate.

import Definitions.Def_mme_omega

universe u
open MME

theorem mme_omega_lt_237134 {K : Type u} [Field K] :
    matMulExp K < 237134 / 100000 := by sorry
