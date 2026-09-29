-- Prove2me | Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
-- name    : mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T00:16:37.238635+00:00
-- url     : https://prove2.me/theorems/932947f8-4431-4750-bf20-743f911ef691
-- title:
--   Unsupported paired cyclic choices have zero tensor projection
-- statement:
--   Let $K$ be a field and let a primary $q=6$ coupled-address family have a common balanced halving. Form the paired source tensor from the twice-cyclically permuted coupled tensor raised to power $N$ and the once-cyclically permuted coupled tensor raised to power $N$.
--
--   Choose a family entry $j_i$ independently in each physical mode $i\in\{0,1,2\}$ and apply that entry's component projection in that mode. If $(j_0,j_1,j_2)$ is not paired cyclic supported, the resulting tensor is zero:
--
--   $$
--   \left(\bigotimes_{i=0}^{2} P_{j_i,i}\right)
--   \left((C^{\circlearrowleft 2})^{\otimes N}
--   \otimes(C^{\circlearrowleft})^{\otimes N}\right)=0.
--   $$
--
--   Thus paired cyclic support is a necessary condition for a nonzero mixed component projection. This statement does not assume paired inducedness or assert that supported mixed projections vanish.
-- source:
--   A derived tensor-algebra bridge for the platform definitions mme_CW_q6_common_halving_paired_oriented_component_data and mme_CW_q6_paired_cyclic_induced. Uses the proved explicit coupled four-block support theorem. The tensor projection induction adapts the accepted proof of mme_induced_graded_address_blocks_restrict to arbitrary finite entry indices. This is a new interface lemma, not a numbered theorem in the source paper.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
open MME MME.PairedOrientedPackaging
universe u
set_option autoImplicit false

theorem mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H)
    (h : ¬ family.PairedCyclicSupported halving (js 0) (js 1) (js 2)) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t = 0 := by sorry
