-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairBobMeanFilter_eq_jointPrefixOperatorFilter
-- name    : QuantumParallelRepetition.exactFairBobMeanFilter_eq_jointPrefixOperatorFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:59:37.308822+00:00
-- url     : https://prove2.me/theorems/bdb9c5a4-7d80-482b-9832-60a1142b4431
-- title:
--   Bob's mean filter equals the joint prefix filter that reveals only Alice's distinguished question
-- statement:
--   Fix a strategy $S$ for $G^{n}$, a coordinate set $D$, and a seed with distinguished coordinate $i\notin D$. For a revealed history $h$ and Bob answers $b\in B^{D}$, Bob's question filter $B^{b}_{h}(y)$ is the normalized average of his conditioned effect operator over the full question tuples compatible with $h$ that assign him the question $y$ at $i$, and his mean filter is $\bar B^{b}_{h}(x)=\sum_{y}\Pr[y\mid x]\,B^{b}_{h}(y)$. Writing $\Lambda^{B}_{F_X,F_Y}(b;q)$ for the conditional expectation of Bob's conditioned effect operator given that the questions agree with $q$ on the $X$-coordinates in $F_X$ and the $Y$-coordinates in $F_Y$, the theorem states that for every full question tuple $q$ of nonzero prior weight,
--   $$\bar B^{b}_{c(q)}\big(q_X(i)\big)=\Lambda^{B}_{M_A\cup\{i\},\,M_B}(b;q),$$
--   where $c(q)$ is the history revealed by $q$ and $M_A,M_B$ are the seed's fair Alice and Bob question masks. This is the exact mirror of the Alice-side identity: averaging Bob's filter over his own unrevealed question is the same as conditioning on Alice's question at the distinguished coordinate but not on Bob's.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L39041-L39134

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
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
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactFairBobMeanFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → B)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactBobMeanFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixBobOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed)
        answer q.1 q.2 := by sorry
