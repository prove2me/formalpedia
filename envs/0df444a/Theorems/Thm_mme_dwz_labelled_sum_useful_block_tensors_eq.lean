-- Prove2me | Theorems.Thm_mme_dwz_labelled_sum_useful_block_tensors_eq
-- name    : mme_dwz_labelled_sum_useful_block_tensors_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:18:47.230992+00:00
-- url     : https://prove2.me/theorems/004bc381-257f-447a-954c-6f7c1e3e8e0d
-- title:
--   The singleton useful-block tensors partition the complete labelled standard tensor
-- statement:
--   Let $D$ be a trilinear standard tensor with a distinguished basis in its $Z$ mode, and assign every distinguished basis vector one useful-block label from a finite set $B$. For $b\in B$, let $D_b$ be the tensor obtained by retaining precisely the Z-basis vectors labelled by $b$ and leaving the X and Y modes unchanged. Then
--
--   $$
--   \sum_{b\in B} D_b = D.
--   $$
--
--   Thus the target produced by the Hole Lemma as a formal sum of all singleton useful-block contributions is literally the complete labelled standard tensor, rather than merely an object of the same cardinality or an abstract isomorphic copy.
--
--   **Formalization Note** The statement is polymorphic in the labelled standard-data bundle and therefore applies directly to the literal fifteen-factor Kronecker representation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.5 and the standard-tensor decomposition used in the Hole Lemma, PDF pp. 47--50 / printed pp. 46--49; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_labelled_sum_useful_block_tensors_eq
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) :
    (∑ block : DWZStandardBlock m,
        dwzLabelledUsefulBlockTensor K m D block) = D.X.t := by
  sorry
