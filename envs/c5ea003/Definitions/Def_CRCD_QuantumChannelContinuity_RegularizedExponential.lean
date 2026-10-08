-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_RegularizedExponential
-- name    : CRCD_QuantumChannelContinuity_RegularizedExponential
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:39:16.818075+00:00
-- url     : https://prove2.me/theorems/e4ef2d5a-0604-4daf-8a63-f82c80795100
-- title:
--   Exponential bounds for regularized Rényi divergence
-- statement:
--   For real $p>1$ and $z>0$, a logarithmic bound $d\le\frac{2p}{p-1}\log_2z$ gives $2^{(p-1)d/(2p)}\le z$. For $D\in[0,\infty]$, the corresponding premise $D\le\operatorname{ofReal}(\frac{2p}{p-1}\log_2z)$ implies finiteness and the same exponential bound on its real representative when $z\ge1$; this additional condition handles truncation by $\operatorname{ofReal}$.
--
--   For CPTP maps on nonzero finite-dimensional complex input, output, and environment spaces, let $V=\sum_iU_i$ be a finite decomposition of a dilation of $N$, with $\mathcal D_{U_i}\preceq_{\mathrm{CP}}\lambda_iM$, $\|U_i\|\le b_i$, and $b_i,\lambda_i\ge0$. For $1<p\le2$,
--
--   $$
--   D_p^{\mathrm{reg}}(N\|M)<\infty,\qquad 2^{\frac{p-1}{2p}D_p^{\mathrm{reg}}(N\|M)}\le\sum_i b_i^{1/p}\lambda_i^{(p-1)/(2p)}.
--   $$
--
--   The finiteness and the lower bound of one on the sum follow from the supplied decomposition; they are not extra hypotheses.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/RegularizedExponential.lean#L25-L82

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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
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
# Exponential form of the actual regularized Schatten estimate

The block-supremum upper bound is converted into the manuscript's exponential
form.  Finiteness, support inclusion, and the lower bound on the sum of weights
are consequences of the supplied dilation decomposition.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- Scalar conversion of a logarithmic Rényi-rate upper bound. -/
theorem rpow_le_of_renyi_log_bound {p d z : ℝ} (hp : 1 < p) (hz : 0 < z)
    (hd : d ≤ (2 * p / (p - 1)) * Real.logb 2 z) :
    (2 : ℝ) ^ ((p - 1) / (2 * p) * d) ≤ z := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  calc
    _ ≤ (2 : ℝ) ^ ((p - 1) / (2 * p) * ((2 * p / (p - 1)) * Real.logb 2 z)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = (2 : ℝ) ^ Real.logb 2 z := by
      congr 1
      field_simp
    _ = z := Real.rpow_logb (by norm_num) (by norm_num) hz

/-- Extended-real version: a finite logarithmic upper bound gives finiteness
and the exponential estimate. The premise `1 ≤ z` handles the truncation in
`ENNReal.ofReal` explicitly. -/
theorem ennreal_rpow_le_of_renyi_log_bound {p z : ℝ} (hp : 1 < p) (hz : 1 ≤ z)
    (D : ℝ≥0∞) (hD : D ≤ ENNReal.ofReal ((2 * p / (p - 1)) * Real.logb 2 z)) :
    D ≠ ⊤ ∧ (2 : ℝ) ^ ((p - 1) / (2 * p) * D.toReal) ≤ z := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hlog : 0 ≤ Real.logb 2 z := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) zero_lt_one hz
  have hL : 0 ≤ (2 * p / (p - 1)) * Real.logb 2 z := by positivity
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD, ?_⟩
  apply rpow_le_of_renyi_log_bound hp hz0
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
  rwa [ENNReal.toReal_ofReal hL] at h

variable {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B] [Nontrivial E]

/-- The actual regularized channel divergence satisfies the exponential
filter–Schatten estimate. All tensor words and entangled inputs are accounted
for by the concrete tensor-power construction; finiteness is proved. -/
theorem regularizedRenyi_dilation_exponential_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    regularizedRenyi p N M ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (regularizedRenyi p N M).toReal) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hchannel := channelRenyi_dilation_exponential_bound hp hp2 N M V hV U hVU
    b lam hb hlam hdom hnorm
  have hsum : 1 ≤ ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) :=
    (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)).trans hchannel.2
  exact ennreal_rpow_le_of_renyi_log_bound hp hsum (regularizedRenyi p N M)
    (regularizedRenyi_dilation_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm)

end QuantumChannelContinuity


