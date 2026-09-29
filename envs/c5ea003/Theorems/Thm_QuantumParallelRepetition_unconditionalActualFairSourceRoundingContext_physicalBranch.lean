-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_physicalBranch
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_physicalBranch
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T22:03:55.248198+00:00
-- url     : https://prove2.me/theorems/8e0cc49d-2070-4d46-a218-3c3d44b93646
-- title:
--   The context's sampled branch mass equals the physical stopping branch mass
-- statement:
--   In the setting of an `UnconditionalActualFairSourceRoundingContext` $c$ for a game $G$, a strategy
--   $S$ on $G^{n}$, a postselected set $D$ and parameters $\alpha, \gamma$: fix a shared source flag
--   $\mathrm{flag}$ over the sampler's denominator, a question pair $(x, y) \in X \times Y$, and
--   suppose the sampled permutation matches, i.e.
--   $\mathrm{exactSourcePermutationMatched}(\mathrm{flag}, (x,y)) = \mathrm{true}$.
--
--   Then, summing over the rounds $j$ of the stopping schedule,
--
--   $$
--   \sum_{j} \big\langle\, c.\mathrm{operator}(t, j),\ c.\mathrm{actual}(t, j) \,\big\rangle_{Q}
--   \;\le\;
--   \sum_{j} \big\langle\, E_{j}(x, y),\ v_{j} \,\big\rangle_{Q},
--   $$
--
--   where $t$ is the Alice sample tuple determined by $\mathrm{flag}$ and $(x,y)$, each
--   $\langle\cdot,\cdot\rangle_{Q}$ is the quadratic expectation, $E_{j}(x,y)$ is the stopping branch
--   winning effect at round $j{+}1$ transported through `Matrix.toEuclideanCLM`, and $v_{j}$ is the
--   branch vector of the local action built from $c.U(\mathrm{flag}, x)$, $c.V(\mathrm{flag}, y)$ and
--   $c.\mathrm{prepared}(\mathrm{flag})$.
--
--   The inequality is in fact an equality: the two sides are the same Born mass written in the
--   sampler's coordinates on the left and in the physical branch coordinates on the right. It is the
--   step that lets the rounding argument, which is carried out on sampled data, be read as a statement
--   about the actual physical protocol.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70679-L70733

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_physicalBranch
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma)
    (flag : ExactSourceSharedFlag
      X Y A B D c.sampler.denominator)
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D c.sampler.denominator c.sampler.numerator
        c.sampler.nonempty (flag, (x, y)) = true) :
    (∑ j : Fin c.stopping.L,
      quadraticExpectation
        (c.operator
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))
        (c.actual
          (exactSourceAliceSampleTuple
            D c.sampler.denominator c.sampler.numerator
            c.sampler.nonempty (flag, (x, y)), j))) ≤
      ∑ j : Fin c.stopping.L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := c.fiber × c.fiber) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G (c.PA flag) (c.PB flag) j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (c.U flag x) (c.V flag y) (c.prepared flag))
            j.succ j.succ) := by sorry
