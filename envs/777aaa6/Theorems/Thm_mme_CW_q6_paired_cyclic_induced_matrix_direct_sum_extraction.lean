-- Prove2me | Theorems.Thm_mme_CW_q6_paired_cyclic_induced_matrix_direct_sum_extraction
-- name    : mme_CW_q6_paired_cyclic_induced_matrix_direct_sum_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T00:40:41.898783+00:00
-- url     : https://prove2.me/theorems/1e11eeee-d5dd-4fbc-8864-09abea727070
-- title:
--   Matrix direct-sum extraction from a paired-induced coupled family
-- statement:
--   Let $K$ be any field, and let a primary $q=6$ coupled-address family have parameters $N,L,G,A,H$ and a common balanced halving. Assume that the family is paired cyclic induced: every supported mixed triple for the two oriented halves selects the same family entry in all three physical modes.
--
--   Then the paired source
--   $$T=\bigl(\operatorname{perm}_{c^2} C_6\bigr)^{\otimes N}\otimes\bigl(\operatorname{perm}_{c} C_6\bigr)^{\otimes N}$$
--   restricts to a direct sum of exactly $AH$ matrix-multiplication tensors. There exist natural dimensions $a_j,b_j,c_j$ indexed by $j\in\operatorname{Fin}(AH)$ such that
--   $$\bigoplus_j\langle a_j,b_j,c_j\rangle\preceq T,
--   \qquad a_jb_jc_j=6^{4G+2L}\quad\text{for every }j.$$
--   The dimensions may vary between entries. The proof uses the literal component projections and eliminates mixed choices by paired inducedness. This is a conditional extraction theorem: primary inducedness and balanced halving alone do not imply its additional paired-inducedness hypothesis.
-- source:
--   Constructive consequence of the platform paired-cyclic-induced and paired-oriented-component definitions. Combines mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported with mme_CW_q6_common_halving_paired_oriented_component_certificate. The direct-sum map construction adapts the accepted proof of mme_induced_graded_address_blocks_restrict (b733f18a-4aae-41fd-a2e9-e945c7328409). No unconditional source-faithful extraction is asserted.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
open MME MME.PairedOrientedPackaging
universe u
set_option autoImplicit false

theorem mme_CW_q6_paired_cyclic_induced_matrix_direct_sum_extraction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) :
    ∃ a b c : Fin (A * H) → ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)) ∧
      ∀ j, a j * b j * c j = 6 ^ (4 * G + 2 * L) := by sorry
