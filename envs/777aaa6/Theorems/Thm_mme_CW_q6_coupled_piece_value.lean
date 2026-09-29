-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_piece_value
-- name    : mme_CW_q6_coupled_piece_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T05:06:36.994781+00:00
-- url     : https://prove2.me/theorems/f0d26183-c9d2-4605-907d-9dbe9822e631
-- title:
--   Symmetric tau-value of the coupled $q=6$ constituent
-- statement:
--   Let $D_6$ be the coupled Coppersmith--Winograd constituent and fix $\tau$ with $3\tau\ge2$. Then its symmetric tau-value is at least
--
--   $$
--   2^{2/3}\,6^{\tau}\bigl(6^{3\tau}+2\bigr)^{1/3}.
--   $$
--
--   Here symmetric value means that the cyclic tensor product $D_6\otimes\pi(D_6)\otimes\pi^2(D_6)$ has ordinary tau-value at least the cube of the displayed expression. This is the exact $q=6$ coupled-piece hypothesis used in the specialized Coppersmith--Winograd auxiliary inequality leading to the $2.376$ exponent bound.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), symmetric value definition on journal p. 264 and coupled-constituent lemma on journal pp. 270--272 (PDF pp. 14, 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_q6_coupled_piece_value
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    HasSymmetricTauValueAtLeast (coupledObj K 6) tau
      ((2 : ℝ) ^ ((2 : ℝ) / 3) *
       (6 : ℝ) ^ tau *
       (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) := by sorry
