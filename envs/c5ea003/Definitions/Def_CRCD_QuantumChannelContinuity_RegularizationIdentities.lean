-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_RegularizationIdentities
-- name    : CRCD_QuantumChannelContinuity_RegularizationIdentities
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:51:16.532016+00:00
-- url     : https://prove2.me/theorems/6e3c5d3e-d21b-4fdd-a66e-0a891c0310de
-- title:
--   Tensor-power scaling and superadditivity of channel divergence
-- statement:
--   For CPTP maps $N,M:A\to B$ on nonzero finite-dimensional complex Hilbert spaces and order $p>1$, the block Rényi quantities $R_p(n)=D_p(N^{\otimes n}\|M^{\otimes n})$, valued in $[0,\infty]$, satisfy
--
--   $$
--   R_p(m)+R_p(n)\le R_p(m+n)\quad(m,n\in\mathbb N).
--   $$
--
--   For every positive integer $n$, regularization scales exactly under grouping into blocks:
--
--   $$
--   D_p^{\mathrm{reg}}(N^{\otimes n}\|M^{\otimes n})=nD_p^{\mathrm{reg}}(N\|M).
--   $$
--
--   These are extended-nonnegative equalities and inequalities and require no finiteness hypothesis. The one-copy channel relative entropy also obeys $D(N\|M)\le D^{\mathrm{reg}}(N\|M)$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/RegularizationIdentities.lean#L26-L79

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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
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

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Superadditivity and exact block scaling of concrete regularization

The identities concern the actual tensor powers and the actual stabilized
channel divergences. Their proof uses product inputs, canonical Hilbert-space
regrouping, and the extended-real supremum argument.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

/-- The stabilized Rényi block sequence is superadditive, including infinities. -/
theorem blockRenyi_superadditive {p : ℝ} (hp : 1 < p) (N M : CPTP A B) (m n : ℕ) :
    blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (m + n) := by
  have h := channelRenyi_tensor_superadditive hp
    (channelPower N m) (channelPower M m) (channelPower N n) (channelPower M n)
  have heq := channelRenyi_isometry (by linarith : 1 / 2 ≤ p) hp.ne'
    (powerConcatIso A m n) (powerConcatIso B m n)
    (tensorChannel (channelPower N m) (channelPower N n))
    (tensorChannel (channelPower M m) (channelPower M n))
    (channelPower N (n + m)) (channelPower M (n + m))
    (powerConcat_intertwine N m n) (powerConcat_intertwine M m n)
  rw [heq] at h
  change blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (n + m) at h
  rwa [Nat.add_comm n m] at h



/-- Exact regularized Rényi block scaling. This is unconditional for every
order above one and every positive block length. -/
theorem regularizedRenyi_power_scaling {p : ℝ} (hp : 1 < p) (N M : CPTP A B)
    {n : ℕ} (hn : 0 < n) :
    regularizedRenyi p (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRenyi p N M := by
  simp only [regularizedRenyi, blockRenyi_power (by linarith : 1 / 2 ≤ p) hp.ne']
  exact ennreal_iSup_div_multiples (blockRenyi p N M) (blockRenyi_superadditive hp N M) hn





theorem channelRelative_le_regularized (N M : CPTP A B) :
    channelRelative N M ≤ regularizedRelative N M := by
  have h := blockRelative_le_regularized N M (n := 1) zero_lt_one
  simpa only [blockRelative_one, Nat.cast_one, mul_one] using h

end QuantumChannelContinuity


