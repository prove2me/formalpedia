-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
-- name    : CRCD_QuantumChannelContinuity_ChannelTesting
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:11:57.184+00:00
-- url     : https://prove2.me/theorems/e478071d-8694-48e1-b27d-f4816b12cec8
-- title:
--   Stabilized channel testing bounds from finite divergence bounds
-- statement:
--   Let $\delta_\gamma(N,M)$ denote the stabilized channel hockey-stick divergence of CPTP maps between nonzero finite-dimensional complex Hilbert spaces. If $\ell>0$, $a\ge0$, and the channel relative entropy satisfies $D(N\|M)\le a$ bits, then
--
--   $$
--   \delta_{2^\ell}(N,M)\le\frac{a+1}{\ell}.
--   $$
--
--   More generally, for $n\ge1$, $r>0$, and $d\ge0$, the premise $D(N\|M)\le nd$ yields $\delta_{2^{nr}}(N,M)\le d/r+1/(nr)$.
--
--   If $\alpha>1$, $a\ge0$, and $D_\alpha(N\|M)\le a$, then for every real $\ell$,
--
--   $$
--   \delta_{2^\ell}(N,M)\le2^{-(\alpha-1)(\ell-a)}.
--   $$
--
--   For every $n\in\mathbb N$, the scaled premise $D_\alpha(N\|M)\le na$ analogously gives $\delta_{2^{n\ell}}(N,M)\le2^{-n(\alpha-1)(\ell-a)}$. These scaled bounds concern any channel pair satisfying the stated divergence premise; that premise is not an implicit assumption about its tensor powers.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ChannelTesting.lean#L23-L62

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
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
# Testing bounds for the actual stabilized channel divergences

The optimizations over both pure entangled inputs and all quantum effects
are discharged here. Only a bound on the channel divergence itself is used.
-/

open QuantumState QuantumChannel
open scoped ENNReal TensorProduct

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- The exponential testing bound for concrete finite-dimensional channels. -/
theorem channelHockey_renyi_bound (N M : CPTP H K) {α ell a : ℝ}
    (hα : 1 < α) (ha : 0 ≤ a) (hD : channelRenyi α N M ≤ ENNReal.ofReal a) :
    channelHockey ((2 : ℝ) ^ ell) N M ≤ (2 : ℝ) ^ (-(α - 1) * (ell - a)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨ψ, rfl⟩
  exact stateHockey_renyi_bound _ _ hα
    (stateRenyi_le_of_channel_le N M (by linarith) (ne_of_gt hα) ha hD ψ)

/-- A block channel satisfying `Dα ≤ n*a` has the exact manuscript high-rate
bound. The block can be any actual CPTP map, including a tensor power. -/
theorem block_channelHockey_renyi_bound (N M : CPTP H K) (n : ℕ)
    {α ell a : ℝ} (hα : 1 < α) (ha : 0 ≤ a)
    (hD : channelRenyi α N M ≤ ENNReal.ofReal ((n : ℝ) * a)) :
    channelHockey ((2 : ℝ) ^ ((n : ℝ) * ell)) N M ≤
      (2 : ℝ) ^ (-(n : ℝ) * (α - 1) * (ell - a)) := by
  have h := channelHockey_renyi_bound N M (ell := (n : ℝ) * ell) hα
    (mul_nonneg (Nat.cast_nonneg n) ha) hD
  convert h using 1; congr 1; ring

/-- The weak testing bound for concrete stabilized channel relative entropy. -/
theorem channelHockey_relative_bound (N M : CPTP H K) {ell a : ℝ}
    (hell : 0 < ell) (ha : 0 ≤ a) (hD : channelRelative N M ≤ ENNReal.ofReal a) :
    channelHockey ((2 : ℝ) ^ ell) N M ≤ a / ell + 1 / ell := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨ψ, rfl⟩
  exact stateHockey_relative_bound _ _ hell
    (stateRelative_le_of_channel_le N M ha hD ψ)

/-- The exact block-size normalization of the concrete weak testing bound. -/
theorem block_channelHockey_relative_bound (N M : CPTP H K) {n : ℕ}
    (hn : 0 < n) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (hD : channelRelative N M ≤ ENNReal.ofReal ((n : ℝ) * d)) :
    channelHockey ((2 : ℝ) ^ ((n : ℝ) * r)) N M ≤ d / r + 1 / ((n : ℝ) * r) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := channelHockey_relative_bound N M (mul_pos hnR hr)
    (mul_nonneg hnR.le hd) hD
  convert h using 1
  congr 1
  field_simp

end QuantumChannelContinuity


