-- Prove2me | Theorems.Thm_mme_CW_q6_paired_oriented_cross_fiber_projection_counterexample
-- name    : mme_CW_q6_paired_oriented_cross_fiber_projection_counterexample
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T00:28:53.606956+00:00
-- url     : https://prove2.me/theorems/cd8c428b-ebea-4d65-b3b1-0ff3293235ae
-- title:
--   A nonzero cross-fiber term in the literal paired tensor projection
-- statement:
--   Over every field $K$, there exists a primary $q=6$ coupled-address family with parameters $N=2$, $L=G=1$, two outer fibers and one entry in each fiber, together with a common balanced halving, for which a cross-fiber mixed tensor projection is nonzero.
--
--   More precisely, let $T$ be the paired source formed from the second powers of the twice-cyclically and once-cyclically permuted coupled tensors. There are entries $p,q$ in distinct outer fibers such that the literal component projections satisfy
--
--   $$
--   (P_{p,0}\otimes P_{p,1}\otimes P_{q,2})T\ne 0.
--   $$
--
--   Thus primary-family inducedness and common balanced halving alone do not make these component maps isolate the outer fibers. The assertion concerns these specified maps; it does not rule out tensor certificates using other maps or other constructions.
-- source:
--   Tensor-level refinement of the accepted two-entry construction in mme_CW_q6_common_halving_paired_cyclic_induced_counterexample (theorem a678fe66-b96e-4706-bb10-9aa61d0fabc6). The finite address family is reproduced from its accepted proof. Nonvanishing follows from mme_CW_q6_paired_oriented_mixed_projection_ne_zero_iff. This is a counterexample to outer-fiber isolation by the literal component projections, not to the open existential certificate targets.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Mathlib.Data.Fin.VecNotation
open MME MME.PairedOrientedPackaging
universe u
set_option autoImplicit false

theorem mme_CW_q6_paired_oriented_cross_fiber_projection_counterexample
    {K : Type u} [Field K] :
    ∃ family : CWQ6PrimaryHashFamily 2 1 1 2 1,
      ∃ halving : family.CommonBalancedXYHalving,
        ∃ p q : Fin 2 × Fin 1, p.1 ≠ q.1 ∧
          PiTensorProduct.map
            (fun i => componentProj (K := K) family halving (![p, p, q] i) i)
            (TensorObj.kron
              ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                (coupledObj K 6)).kronPow 2)
              ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow 2)).t ≠ 0 := by sorry
