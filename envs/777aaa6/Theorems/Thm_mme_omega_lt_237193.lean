-- Prove2me | Theorems.Thm_mme_omega_lt_237193
-- name    : mme_omega_lt_237193
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:01:36.101689+00:00
-- url     : https://prove2.me/theorems/5358c0de-24dd-4405-9bb7-53bf5e0b7dcc
-- title:
--   Duan–Wu–Zhou fourth-power bound: omega < 2.37193
-- statement:
--   For every field K, the existing matrix-multiplication exponent matMulExp K is strictly less than 237193/100000 = 2.37193. There are no characteristic, witness, or tensor-value hypotheses.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Table 3 (printed p.78), fourth-power row. Rounded upward to an exact rational endpoint. https://arxiv.org/abs/2210.10173v5

import Definitions.Def_mme_omega

universe u

open MME

theorem mme_omega_lt_237193 {K : Type u} [Field K] :
    matMulExp K < 237193 / 100000 := by sorry
