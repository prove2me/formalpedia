-- Prove2me | Theorems.Thm_mme_omega_lt_23737
-- name    : mme_omega_lt_23737
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-29T00:21:16.90877+00:00
-- url     : https://prove2.me/theorems/5530eb43-e9fb-40a9-b036-2236a694a3fd
-- title:
--   Davie--Stothers fourth-power bound: omega < 2.3737
-- statement:
--   Let $K$ be an arbitrary field and let $\omega(K)$ denote the exponent of square matrix multiplication over $K$. Then
--
--   $$
--   \omega(K)<\frac{23737}{10000}=2.3737.
--   $$
--
--   This is a strict exact-rational consequence of the Davie--Stothers fourth-power analysis, which reports the stronger numerical endpoint $2.373689703$. The theorem is the historical first improvement obtained by passing from the square to the fourth power of the Coppersmith--Winograd tensor.
--
--   **Formalization Note** The statement uses the established field-uniform `matMulExp` definition and imposes no characteristic restriction on $K$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Theorem 5.3 and Table 2, printed pp. 367-368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf; DOI 10.1017/S0308210511001646.

import Definitions.Def_mme_omega

universe u

open MME

set_option autoImplicit false

theorem mme_omega_lt_23737 {K : Type u} [Field K] :
    matMulExp K < 23737 / 10000 := by sorry
