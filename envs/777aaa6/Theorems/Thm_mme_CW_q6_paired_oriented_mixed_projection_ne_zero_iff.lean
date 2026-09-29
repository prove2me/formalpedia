-- Prove2me | Theorems.Thm_mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
-- name    : mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T00:27:37.419018+00:00
-- url     : https://prove2.me/theorems/0d586813-c844-4b1a-b7bf-c802f1c2f193
-- title:
--   Exact support of paired oriented mixed tensor projections
-- statement:
--   Let $K$ be any field, and let a primary $q=6$ coupled-address family have a common balanced halving. Write $T$ for the paired source formed from the $N$th powers of the twice-cyclically and once-cyclically permuted coupled tensors. Let $P_{p,i}$ be the component projection associated with family entry $p$ in physical mode $i$.
--
--   Choose entries $j_0,j_1,j_2$ independently in the three modes. Then
--
--   $$
--   \left(\bigotimes_{i=0}^{2}P_{j_i,i}\right)T\ne 0
--   \quad\Longleftrightarrow\quad
--   (j_0,j_1,j_2)\text{ is paired cyclic supported}.
--   $$
--
--   The support condition requires all coordinate triples to belong to the four allowed coupled types, with choices $(j_2,j_0,j_1)$ in the first half and $(j_1,j_2,j_0)$ in the second half. Thus the address predicate is an exact criterion for survival of the literal mixed projection, including in positive characteristic. No paired-inducedness assumption is imposed.
-- source:
--   New exact-support interface theorem for the platform definitions mme_CW_q6_common_halving_paired_oriented_component_data and mme_CW_q6_paired_cyclic_induced. Combines the previously proved mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported with the accepted explicit coupled four-block isomorphisms and a product-basis nonvanishing argument. Not a numbered theorem from a source paper.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
open MME MME.PairedOrientedPackaging
universe u
set_option autoImplicit false

theorem mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ≠ 0 ↔
      family.PairedCyclicSupported halving (js 0) (js 1) (js 2) := by sorry
