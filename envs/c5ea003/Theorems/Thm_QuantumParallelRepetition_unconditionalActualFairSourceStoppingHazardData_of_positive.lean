-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceStoppingHazardData_of_positive
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceStoppingHazardData_of_positive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:46:48.269677+00:00
-- url     : https://prove2.me/theorems/3589f1b3-1f52-40dc-8549-d5fbb8590bad
-- title:
--   The stopping-hazard record is inhabited
-- statement:
--   Let $G$, $n$, $S$, $D$ be as usual with a remaining coordinate and positive postselection mass, and let
--   $\alpha \in (0,1]$ satisfy $64\sqrt{\eta} + \alpha^{1/3} \le 1$, where $\eta$ is the martingale rate. Then the
--   bundle of stopping-hazard data at accuracy $\alpha$ is nonempty: there exist a width $w \ge 1$, a positive grid
--   $N$, a horizon $L$, a positive phase count $P$, gauge parameters $Q$ and $m > 0$, and unitary families $U^A, U^B$
--   satisfying the fineness condition $d/N < 1/(w+1)$ and the scalar condition $1/w + dw/N \le \tfrac32\alpha^{1/3}$
--   (with $d$ the size of the global history local index), such that, averaged over the locally sampleable law, the
--   asynchronous stopping mass is at most $64\sqrt{\eta}+\alpha^{1/3}$, the terminal mass is at most
--   $(\alpha^{1/3})^2$, and the common-prefix hazard is at most
--   $\frac{34}{t}\bigl(64\sqrt{\eta}+\alpha^{1/3}\bigr) + 4\alpha^{1/6} + \kappa\, t$ with
--   $t = \sqrt{64\sqrt{\eta}+\alpha^{1/3}}$ and $\kappa = 16(e-1)+4$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L69853-L69892

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceStoppingHazardData_of_positive
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (alpha : ℝ) (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt (martingaleRate G n S D) +
      alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Nonempty (UnconditionalActualFairSourceStoppingHazardData
      G n S D alpha) := by sorry
