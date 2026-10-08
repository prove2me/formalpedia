-- Prove2me | Theorems.Thm_QuantumChannelContinuity_blockRenyi_tendsto_regularized
-- name    : QuantumChannelContinuity.blockRenyi_tendsto_regularized
-- status  : Proved
-- author  : @JWang226
-- created : 2026-10-08T04:12:10.871214+00:00
-- url     : https://prove2.me/theorems/cd681e1d-c17b-4b84-be88-a20cdbe993bd
-- title:
--   Equation (1.5) — Rényi regularization as a normalized block limit
-- statement:
--   Let $A$ and $B$ be nonzero finite-dimensional complex Hilbert spaces, let $N,M:\mathcal L(A)\to\mathcal L(B)$ be completely positive, trace-preserving maps, and fix a real order $\alpha\ge1/2$ with $\alpha\ne1$. For each positive integer $n$, let $\widetilde D_\alpha(N^{\otimes n}\Vert M^{\otimes n})$ be the stabilized sandwiched Rényi divergence in bits, optimized over normalized pure inputs with a reference copy of $A^{\otimes n}$.
--
--   Define
--
--   $$
--   \widetilde D_\alpha^{\mathrm{reg}}(N\Vert M)
--   =\sup_{n\ge1}\frac{\widetilde D_\alpha(N^{\otimes n}\Vert M^{\otimes n})}{n}.
--   $$
--
--   Then
--
--   $$
--   \lim_{n\to\infty}\frac{\widetilde D_\alpha(N^{\otimes n}\Vert M^{\otimes n})}{n}
--   =\widetilde D_\alpha^{\mathrm{reg}}(N\Vert M).
--   $$
--
--   Convergence takes place in $[0,+\infty]$, including infinite individual block values and an infinite supremum. This establishes the Rényi instance of the paper's regularization identity at every admissible order other than one. Inputs may be entangled across all $n$ uses.
--
--   **Formalization Note** Lean defines the block sequence at zero as well; that totalized value is irrelevant to the limit at infinity and is excluded from the defining positive-block supremum.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/RegularizationLimits.lean#L116-L123

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ENNReal.Inv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_Quantum_QuantumEntropy_CFCDeriv
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelProducts
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_PowerRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationIdentities
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationSup
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorNaturality
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorStates
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-!
# Identification of block suprema with the manuscript's limits

Tensor additivity and superadditivity also hold below one, including the
orthogonal-support infinite convention. Extended Fekete then identifies the
actual regularized quantities with their normalized block limits at every
admissible Rényi order.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity
end QuantumChannelContinuity
open QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]










variable {A B C D : Type} [Qudit A] [Qudit B] [Qudit C] [Qudit D]
  [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

theorem QuantumChannelContinuity.blockRenyi_tendsto_regularized {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) :
    Tendsto (fun n : ℕ => blockRenyi p N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRenyi p N M)) := by sorry
