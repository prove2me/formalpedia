-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
-- name    : mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-27T10:47:33.335743+00:00
-- url     : https://prove2.me/theorems/0587a569-464b-4ea8-a33e-9090ad510117
-- title:
--   Rows 121/211: paired C-tensor certificate from a common balanced primary family
-- statement:
--   Fix the $q=6$ Table-2 component of shape $121$ or $211$ and take its literal allowed-word power at multiplier $m$, paired with the copy obtained by swapping the first two tensor modes. Let an induced primary family with parameters $L,G,A,H$ be supplied on the resulting $2N$ coupled positions. Assume the family has one common balanced halving shared by all its entries: first-mode words are balanced on the first source half and second-mode words are balanced on the second source half.
--
--   Then the paired restricted source maps to a modewise direct sum of $A$ C-tensors over $\langle1,H,1\rangle$. Every one of their $H$ matrix-multiplication components has common volume
--
--   $$6^{4G+2L}.$$
--
--   The individual component shapes may differ. This heterogeneous conclusion is the source-faithful form needed before cyclic balancing; it does not assert a fixed rectangular orientation. The common-halving premise ensures that all mixed choices use one position reindexing, so the original induced-family condition remains applicable and both restricted Z-word profiles are respected.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent and C-tensor extraction on journal pp. 266-271; Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2-5.4 and the rotated 121/211 analysis in Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_common_paired_halving
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    Nonempty (CTensorOneHOneFamilyCertificate
      (TensorObj.kron (restrictedComponentPower K s m)
        (TensorObj.permObj swapFirstTwoPerm
          (restrictedComponentPower K s m)))
      A H (6 ^ (4 * G + 2 * L))) := by
  sorry
