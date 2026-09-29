-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_analyticLedger
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_analyticLedger
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:53:06.602862+00:00
-- url     : https://prove2.me/theorems/961c542e-0f4b-40c7-85e5-aefafe2582fe
-- title:
--   A fair-source rounding context satisfies the stopped analytic ledger
-- statement:
--   Let $c$ be a fair-source rounding context for $(G,n,S,D,\alpha,\gamma)$, with sampling law $\mu$ on locally sampleable histories $h$, branch index $j\in\{1,\dots,L\}$, and three families of branch vectors in the associated Hilbert spaces: the *actual* (cleaned) vectors, the *canonical* (grid-rounded) vectors and the *source* vectors. Let $\mathrm{dev}(c)$ and $\mathrm{clip}(c)$ be its deviation and clipping scalars and put $\mathrm{bad}(c) := 64\sqrt{\lambda}+\alpha^{1/3}+\big(\alpha^{1/3}\big)^{2}$, where $\lambda$ is the martingale rate of $(G,n,S,D)$. The theorem states that these data form an *analytic ledger*, i.e. all seven of the following hold:
--   $$\sum_h \mu(h)\sum_j\|\mathrm{actual}(h,j)\|^2\le 1,\qquad \sum_h \mu(h)\sum_j\|\mathrm{canonical}(h,j)\|^2\le 1,\qquad \sum_j\|\mathrm{canonical}(h,j)\|^2\le 1 \ \ \forall h;$$
--   $\|\mathrm{source}(h,j)\|=\|\mathrm{canonical}(h,j)\|$ for all $h,j$; the two weighted squared distances
--   $\sum_h\mu(h)\sum_j\|\mathrm{actual}-\mathrm{canonical}\|^2\le\mathrm{dev}(c)$ and $\sum_h\mu(h)\sum_j\|\mathrm{canonical}-\mathrm{source}\|^2\le\mathrm{clip}(c)$; and finally the surviving-mass bound $1-\mathrm{bad}(c)\le\sum_h\mu(h)\sum_j\|\mathrm{actual}(h,j)\|^2$. This packages every purely analytic (game-independent) fact needed by the stopping-transfer argument into a single record.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70500-L70609

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Defs.Filter
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
open UnconditionalActualFairSourceRoundingContext
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_analyticLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedStoppedAnalyticLedger
      (law c) (actual c) (canonical c) (source c)
      (deviation c) (clipping c) (bad c) := by sorry
