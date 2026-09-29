-- Prove2me | Theorems.Thm_mme_omega_lt_237465
-- name    : mme_omega_lt_237465
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T18:05:38.678934+00:00
-- url     : https://prove2.me/theorems/43a16f51-54a2-4414-8aa2-493f95fd470b
-- title:
--   Asymmetric hashing square retune: omega < 2.37465
-- statement:
--   Let $K$ be an arbitrary field, and let $\omega(K)$ denote the exponent of square matrix multiplication over $K$. Then
--
--   $$
--   \omega(K)<2.37465.
--   $$
--
--   This is a conservative exact-rational endpoint for the square-power asymmetric-hashing analysis of the Coppersmith--Winograd tensor with parameter $q=6$. It slightly sharpens the previously formalized $2.3747$ endpoint while retaining the same tensor construction and field-uniform conclusion.
--
--   **Formalization Note** The decimal endpoint is represented exactly as $237465/100000$; no characteristic restriction is imposed on $K$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3 and Table 2 (printed pp. 58-59), and the square-power numerical bound in Section 8.3, Table 3 (printed p. 78); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_omega

open MME

universe u

set_option autoImplicit false

theorem mme_omega_lt_237465 {K : Type u} [Field K] :
    matMulExp K < (237465 : ℝ) / 100000 := by sorry
