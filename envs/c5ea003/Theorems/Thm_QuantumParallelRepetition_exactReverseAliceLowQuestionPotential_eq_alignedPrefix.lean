-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceLowQuestionPotential_eq_alignedPrefix
-- name    : QuantumParallelRepetition.exactReverseAliceLowQuestionPotential_eq_alignedPrefix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T05:04:53.76809+00:00
-- url     : https://prove2.me/theorems/a0581060-a021-49e0-bc24-53b0d4cf6d34
-- title:
--   Alice's low question potential coincides with the aligned prefix potential at the marker
-- statement:
--   Fix a strategy $S$ for $G^{n}$ and a coordinate set $D$; let $\mathrm{side}$ be a set of coordinates outside $D$ carrying an ordering context (a ranking of $\mathrm{side}$, a ranking of its complement, a cut in the complement, and a bit), and let $m$ be a marker in $\{0,\dots,\lvert\mathrm{side}\rvert-1\}$, from which a sampling seed with distinguished coordinate $i$ is decoded. Alice's low question potential at $m$ is
--   $$\sum_{q}\pi_n(q)\sum_{a,b}\mathbf{1}[\text{accept}]\;\Big\langle\rho,\;f\big(\bar A^{a}_{c(q)}(q_Y(i))\big)\otimes B^{b}_{c(q)}(q_Y(i))\Big\rangle,$$
--   where $f(z)=z\log z$ is applied through the continuous functional calculus, $\bar A$ is Alice's mean filter, $B$ is Bob's question filter, and $\langle\rho,\,\cdot\otimes\cdot\rangle$ is the Born pairing $\operatorname{Re}\operatorname{tr}\big(\rho(\cdot\otimes\cdot)\big)$ against the shared state. Alice's aligned prefix potential at level $k$ is the same expression with both filters replaced by joint prefix filters conditioning on the $X$-coordinates of Alice's length-$k$ prefix mask and the $Y$-coordinates of the fixed $Y$-mask. The theorem asserts that these two quantities agree, the low question potential at marker $m$ being the aligned prefix potential at level $k=m$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L39250-L39311

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

theorem QuantumParallelRepetition.exactReverseAliceLowQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceLowQuestionPotential
        G n S D side context marker =
      exactReverseAliceAlignedCfcPrefixPotential
        G n S D side context marker.val := by sorry
