-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_survivor_MM_restrict
-- name    : mme_CW_q6_coupled_survivor_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:36:01.829322+00:00
-- url     : https://prove2.me/theorems/e28625f5-e428-4cb8-8cd7-6f41f32888a6
-- title:
--   A coupled q=6 survivor is square matrix multiplication of side $6^{4G+2L}$
-- statement:
--   Let $K$ be a field and let $L,G\in\mathbb N$. One survivor in the coupled $q=6$ extraction consists of $2G$ copies of the cyclic high constituent and $2L$ copies of the cyclic low constituent. It restricts to the square matrix-multiplication tensor
--
--   $$
--   \left\langle 6^{4G+2L},6^{4G+2L},6^{4G+2L}\right\rangle_K\;\le\;\operatorname{coupledQ6Survivor}_K(L,G).
--   $$
--
--   Thus every survivor has square side length $6^{4G+2L}$ and matrix-product volume $6^{12G+6L}$. This identifies the algebraic payload of one block after pruning; the number and disjointness of survivors belong to the separate Salem--Spencer extraction theorem.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent lemma and survivor calculation on journal pp. 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_coupled_cyclic_high_MM_restrict
import Theorems.Thm_mme_CW_coupled_cyclic_low_MM_restrict
import Theorems.Thm_mme_restrict_kronPow
open MME
universe u

theorem mme_CW_q6_coupled_survivor_MM_restrict
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Restrict
      (MMObj K
        (6 ^ (4 * G + 2 * L))
        (6 ^ (4 * G + 2 * L))
        (6 ^ (4 * G + 2 * L)))
      (coupledQ6Survivor K L G) := by sorry
