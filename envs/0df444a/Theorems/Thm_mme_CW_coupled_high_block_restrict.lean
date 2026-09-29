-- Prove2me | Theorems.Thm_mme_CW_coupled_high_block_restrict
-- name    : mme_CW_coupled_high_block_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:41:41.506804+00:00
-- url     : https://prove2.me/theorems/857aca9b-272b-4160-a552-46ead0ece2b2
-- title:
--   The high-volume block of the coupled CW constituent
-- statement:
--   Let $D_q$ be the four-sum coupled Coppersmith--Winograd constituent from the lemma on journal p. 270. Zero all coordinates except the third displayed sum
--
--   $$
--   \sum_{i,k=1}^{q} x_i y_k z_{i,k}.
--   $$
--
--   The surviving tensor is the matrix-multiplication tensor $\langle q,1,q\rangle$. Equivalently, there are explicit modewise linear maps witnessing
--
--   $$
--   \langle q,1,q\rangle \;\leq_{\mathrm{Restrict}}\; D_q.
--   $$
--
--   This identifies one of the high-volume algebraic blocks used three times, with cyclic mode permutations, in the coupled Salem--Spencer extraction. The statement retains the concrete tensor restriction rather than recording only its volume $q^2$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled tensor displayed in the lemma on journal p. 270 (PDF p. 20), specifically its third sum; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_coupled_high_block_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K q 1 q) (coupledObj K q) := by sorry
