-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceExponential
-- name    : CRCD_QuantumChannelContinuity_ThreePieceExponential
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:43:47.507341+00:00
-- url     : https://prove2.me/theorems/e27bcd75-1e3c-4eac-803b-1a3f680e61ab
-- title:
--   The three-piece regularized Rényi exponential estimate
-- statement:
--   For CPTP maps on nonzero finite-dimensional complex input, output, and environment spaces, fix a dilation $V$ of $N$, thresholds $0\le\gamma_l\le\gamma_h\le C$, and complete-positive domination $N\preceq_{\mathrm{CP}}CM$. Assume the exact slack-attainment propositions $\mathrm{HockeySlackAttainment}(\gamma_l,N,M)$ and $\mathrm{HockeySlackAttainment}(\gamma_h,N,M)$. Put $\delta_l=\delta_{\gamma_l}(N,M)$, $\delta_h=\delta_{\gamma_h}(N,M)$, and $\beta=(p-1)/(2p)$. For $1<p\le2$, the regularized divergence is finite and
--
--   $$
--   2^{\beta D_p^{\mathrm{reg}}(N\|M)}\le(1+\sqrt{\delta_l})^{1/p}\gamma_l^\beta+(\sqrt{\delta_l}+\sqrt{\delta_h})^{1/p}(4\gamma_h)^\beta+(\sqrt{\delta_h})^{1/p}(4C)^\beta.
--   $$
--
--   The two attainment propositions are explicit premises of this auxiliary estimate, even though separate attainment theorems can discharge them. The final coefficient is the $1/p$-power of $\sqrt{\delta_h}$, as written; all Rényi divergences and exponential factors use bits.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ThreePieceExponential.lean#L23-L78

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
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizedExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceFilter
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
# The three-piece regularized estimate in exponential form

The low and high filters, all tensor words, reference amplification, support
conditions, and passage to the block supremum are proved. Exact CP-slack
attainment and the channel domination cap remain the explicit input premises.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

/-- The manuscript's three-term exponential bound on the actual regularized
channel Rényi divergence, with finiteness proved at the same time. -/
theorem hockey_three_piece_regularized_exponential
    {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
    [Nontrivial A] [Nontrivial B] [Nontrivial E]
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E) (γlow γhigh C : ℝ)
    (hγlow : 0 ≤ γlow) (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    regularizedRenyi p N M ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (regularizedRenyi p N M).toReal) ≤
      (1 + Real.sqrt (channelHockey γlow N M)) ^ (1 / p) * γlow ^ ((p - 1) / (2 * p)) +
      (Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M)) ^ (1 / p) *
        (4 * γhigh) ^ ((p - 1) / (2 * p)) +
      Real.sqrt (channelHockey γhigh N M) ^ (1 / p) * (4 * C) ^ ((p - 1) / (2 * p)) := by
  classical
  obtain ⟨X, W, hsum, hX, hWX, hVW, hXcp, hWXcp, hVWcp⟩ :=
    hockey_three_piece_decomposition N M V γlow γhigh C hγlow hγle hγC
      hV hcap hlow hhigh
  let U : Fin 3 → A →ₗ[ℂ] B ⊗[ℂ] E := ![X, W - X, V - W]
  let b : Fin 3 → ℝ := ![1 + Real.sqrt (channelHockey γlow N M),
    Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M),
    Real.sqrt (channelHockey γhigh N M)]
  let lam : Fin 3 → ℝ := ![γlow, 4 * γhigh, 4 * C]
  have hsumU : V = ∑ i, U i := by
    simp [U, Fin.sum_univ_succ]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> simp [b] <;> positivity
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    fin_cases i <;> simp [lam]
    · exact hγlow
    · exact hγlow.trans hγle
    · exact (hγlow.trans hγle).trans hγC
  have hsmul (c : ℝ) : (c : ℂ) • M.toLinearMap = c • M.toLinearMap :=
    IsScalarTower.algebraMap_smul ℂ c M.toLinearMap
  rw [hsmul] at hXcp hWXcp hVWcp
  have hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap) := by
    intro i
    fin_cases i
    · simpa [U, lam] using hXcp
    · simpa [U, lam] using hWXcp
    · simpa [U, lam] using hVWcp
  have hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i := by
    intro i
    fin_cases i
    · exact hX
    · exact hWX
    · exact hVW
  have h := regularizedRenyi_dilation_exponential_bound hp hp2 N M V hV U hsumU
    b lam hb hlam hdom hnorm
  simpa [b, lam, Fin.sum_univ_succ, add_assoc] using h

end QuantumChannelContinuity


