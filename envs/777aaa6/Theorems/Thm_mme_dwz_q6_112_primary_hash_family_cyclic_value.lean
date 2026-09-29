-- Prove2me | Theorems.Thm_mme_dwz_q6_112_primary_hash_family_cyclic_value
-- name    : mme_dwz_q6_112_primary_hash_family_cyclic_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:07:33.320197+00:00
-- url     : https://prove2.me/theorems/14253d10-0c15-4c53-92ab-7e55a22bc1a7
-- title:
--   DWZ 112 restricted splitting: cyclic C-tensor value of a primary hash family
-- statement:
--   Let an induced primary hash family in the `2N`-th power of the coupled q=6 constituent have `A` shared-Z fibers of common size `H` and exact profile `(L,L,2G)`. Every nonnegative value strictly below
--
--   $$
--   A^3H^2\,\bigl((6^{4G+2L})^3\bigr)^\tau
--   $$
--
--   is a witnessed tau-value of the cyclic symmetrization of that restricted power. Each fiber is treated as a genuine C-tensor whose components may have different matrix dimensions but have common volume $6^{4G+2L}$.
--
--   For $L+G=N$, the underlying joint split is $(L,L,G,G)/(2N)$ and the Z marginal is $(L/(2N),G/N,L/(2N))$. Thus this is the finite tensor-value payload of the parameter-uniform 112 analysis used with Table 2's $b=0.00021015$; constructing and counting the hash family is a separate combinatorial input.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Appendix A, proof of Lemma 4.6(d), PDF pp. 82-83 / printed pp. 81-82, reused in Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_CW_q6_primary_hash_family_Ctensor_certificates
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_cyclic_value_below

open MME

universe u

theorem mme_dwz_q6_112_primary_hash_family_cyclic_value
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (N L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
        ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast
      (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
      tau V := by sorry
