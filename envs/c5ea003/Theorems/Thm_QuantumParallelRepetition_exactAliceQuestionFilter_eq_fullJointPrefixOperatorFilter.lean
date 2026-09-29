-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
-- name    : QuantumParallelRepetition.exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T05:32:53.336696+00:00
-- url     : https://prove2.me/theorems/baae8a18-a341-4ad5-81f0-5bbda27a3ab5
-- title:
--   Alice's question filter as a joint prefix filter with both distinguished questions fixed
-- statement:
--   Fix a strategy $S$ for $G^{n}$, a coordinate set $D$, a seed with distinguished coordinate $i\notin D$, Alice answers $a\in A^{D}$, and a full question tuple $q=(q_X,q_Y)$ whose weight under $G^{n}$ is nonzero. Let $M_A,M_B$ be the seed's fair Alice and Bob question masks and $c(q)$ the history revealed by $q$. Then Alice's question filter at that history, evaluated at her own question $q_X(i)$, is the joint prefix filter that conditions on the questions agreeing with $q$ on the $X$-coordinates of $M_A\cup\{i\}$ and on the $Y$-coordinates of $M_B\cup\{i\}$:
--   $$A^{a}_{c(q)}\big(q_X(i)\big)=\Lambda^{A}_{M_A\cup\{i\},\,M_B\cup\{i\}}(a;q).$$
--   Equivalently, for a tuple in the support of the prior, additionally revealing Bob's question at the distinguished coordinate leaves Alice's filter unchanged.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L39392-L39431

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactAliceQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by sorry
