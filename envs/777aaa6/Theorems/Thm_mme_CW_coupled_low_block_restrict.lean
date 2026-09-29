-- Prove2me | Theorems.Thm_mme_CW_coupled_low_block_restrict
-- name    : mme_CW_coupled_low_block_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:55:57.352258+00:00
-- url     : https://prove2.me/theorems/2bc37289-1785-4cff-bbc6-a48a4a805473
-- title:
--   A low-volume block of the coupled CW constituent
-- statement:
--   Let $D_q$ be the four-sum coupled Coppersmith--Winograd constituent from the lemma on journal p. 270. Zero all coordinates except its first displayed sum
--
--   $$
--   \sum_{i=1}^{q} x_i y_i z_0.
--   $$
--
--   The surviving diagonal tensor is the matrix-multiplication tensor $\langle1,q,1\rangle$. Thus explicit modewise linear maps witness
--
--   $$
--   \langle1,q,1\rangle\;\leq_{\mathrm{Restrict}}\;D_q.
--   $$
--
--   This is one of the low-volume algebraic blocks used in the coupled Salem--Spencer extraction. The statement retains its concrete restriction witness and matrix-product volume $q$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled tensor displayed in the lemma on journal p. 270 (PDF p. 20), specifically its first sum; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_coupled_low_block_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 q 1) (coupledObj K q) := by sorry
