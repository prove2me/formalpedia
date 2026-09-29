-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactFairAliceMeanFilter_eq_jointPrefixOperatorFilter
-- name    : QuantumParallelRepetition.exactFairAliceMeanFilter_eq_jointPrefixOperatorFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:49:08.151477+00:00
-- url     : https://prove2.me/theorems/2b784448-0a2b-449c-a510-00699fdfeffa
-- title:
--   Alice's mean filter equals the joint prefix filter that reveals only Bob's distinguished question
-- statement:
--   Fix a strategy $S$ for $G^{n}$, a coordinate set $D$, and a seed for the coordinates outside $D$ with distinguished coordinate $i$. For a revealed history $h$ and Alice answers $a\in A^{D}$, Alice's question filter $A^{a}_{h}(x)$ is the normalized average of her conditioned effect operator over all full question tuples compatible with $h$ that assign her the question $x$ at $i$, and her mean filter is $\bar A^{a}_{h}(y)=\sum_{x}\Pr[x\mid y]\,A^{a}_{h}(x)$, the average against the conditional distribution of Alice's question given Bob's question $y$. Separately, for sets $F_X,F_Y\subseteq\{1,\dots,n\}$ the joint prefix filter $\Lambda^{A}_{F_X,F_Y}(a;q)$ is the conditional expectation of the same effect operator given that the questions agree with a tuple $q$ on the $X$-coordinates in $F_X$ and on the $Y$-coordinates in $F_Y$, normalized by the corresponding question mass. The theorem states that for every full question tuple $q$ of nonzero prior weight,
--   $$\bar A^{a}_{c(q)}\big(q_Y(i)\big)=\Lambda^{A}_{M_A,\,M_B\cup\{i\}}(a;q),$$
--   where $c(q)$ is the history revealed by $q$ and $M_A,M_B$ are the seed's fair Alice and Bob question masks. Averaging Alice's filter over her own unrevealed question therefore coincides with conditioning on Bob's question at the distinguished coordinate while leaving Alice's free.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L38947-L39039

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

theorem QuantumParallelRepetition.exactFairAliceMeanFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactAliceMeanFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.2 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by sorry
