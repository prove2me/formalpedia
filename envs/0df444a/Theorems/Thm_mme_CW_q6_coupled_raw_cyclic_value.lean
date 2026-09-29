-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value
-- name    : mme_CW_q6_coupled_raw_cyclic_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T05:06:08.256266+00:00
-- url     : https://prove2.me/theorems/66f931f8-056e-4111-88fa-3e9227d03d7f
-- title:
--   Raw cyclic tau-value of the coupled $q=6$ constituent
-- statement:
--   Let $D_6$ be the explicit four-sum coupled Coppersmith--Winograd constituent and fix $\tau$ with $3\tau\ge2$. Its cyclic symmetrization has tau-value at least
--
--   $$
--   4\,6^{3\tau}(6^{3\tau}+2).
--   $$
--
--   Equivalently, along the cofinal even tensor powers there are concrete restrictions onto finite direct sums of matrix-multiplication tensors whose weighted volumes approach this base exponentially. This theorem is the exact asymptotic wrapper around the witness-level Salem--Spencer extraction and retains the ordinary tau-value convention needed by the formal definition of symmetric value.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-constituent lemma and its proof on journal pp. 270--272 (PDF pp. 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_q6_coupled_raw_cyclic_value
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) := by sorry
