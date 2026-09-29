-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobLowQuestionPotential_eq_alignedPrefix
-- name    : QuantumParallelRepetition.exactReverseBobLowQuestionPotential_eq_alignedPrefix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T05:21:53.875639+00:00
-- url     : https://prove2.me/theorems/aaf5efeb-9085-4540-bec5-bf66a12c35b6
-- title:
--   Bob's low question potential coincides with the aligned prefix potential at the marker
-- statement:
--   With $S$ a strategy for $G^{n}$, $D$ a coordinate set, $\mathrm{side}$ a set of coordinates outside $D$ with an ordering context, and $m$ a marker in $\{0,\dots,\lvert\mathrm{side}\rvert-1\}$ decoding to a seed with distinguished coordinate $i$, Bob's low question potential at $m$ is
--   $$\sum_{q}\pi_n(q)\sum_{a,b}\mathbf{1}[\text{accept}]\;\Big\langle\rho,\;A^{a}_{c(q)}(q_X(i))\otimes f\big(\bar B^{b}_{c(q)}(q_X(i))\big)\Big\rangle,$$
--   with $f(z)=z\log z$ applied by continuous functional calculus, $A$ Alice's question filter, $\bar B$ Bob's mean filter, and $\langle\rho,\,\cdot\otimes\cdot\rangle$ the Born pairing against the shared state. Bob's aligned prefix potential at level $k$ is the same expression with the two filters replaced by joint prefix filters conditioning on the fixed $X$-mask and on Bob's length-$k$ prefix $Y$-mask. The theorem asserts that Bob's low question potential at marker $m$ equals his aligned prefix potential at level $k=m$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L39313-L39374

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseBobLowQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobLowQuestionPotential
        G n S D side context marker =
      exactReverseBobAlignedCfcPrefixPotential
        G n S D side context marker.val := by sorry
