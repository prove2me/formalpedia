-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceFilter
-- name    : CRCD_QuantumChannelContinuity_ThreePieceFilter
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:01:39.773486+00:00
-- url     : https://prove2.me/theorems/d0f010be-e9a5-4f28-93d9-784a03fe6cb1
-- title:
--   Three-component dilation filtering from hockey-stick slack
-- statement:
--   For CPTP maps with nonzero finite-dimensional complex input/output, fix a dilation $V:A\to B\otimes E$, thresholds $0\le\gamma_l\le\gamma_h\le C$, and domination $N\preceq_{\mathrm{CP}}CM$. Assume exact slack attainment at $\gamma_l$ and $\gamma_h$, and set $\delta_l=\delta_{\gamma_l}(N,M)$, $\delta_h=\delta_{\gamma_h}(N,M)$. There exist dilation maps $X,W$ with
--
--   $$
--   V=X+(W-X)+(V-W),
--   $$
--
--
--   $$
--   \|X\|\le1+\sqrt{\delta_l},\quad\|W-X\|\le\sqrt{\delta_l}+\sqrt{\delta_h},\quad\|V-W\|\le\sqrt{\delta_h},
--   $$
--
--
--   $$
--   \mathcal D_X\preceq_{\mathrm{CP}}\gamma_lM,\quad\mathcal D_{W-X}\preceq_{\mathrm{CP}}4\gamma_hM,\quad\mathcal D_{V-W}\preceq_{\mathrm{CP}}4CM.
--   $$
--
--   Here $\mathcal D_U(Z)=\operatorname{Tr}_E(UZU^\dagger)$, and norms are operator norms. Supplied elementary facts give $\|V\|\le1$, $\mathcal D_{U-W}\preceq_{\mathrm{CP}}4rM$ from two dominations by $rM$, addition/nonnegative scaling of CP order, and $r\Phi\preceq_{\mathrm{CP}}s\Phi$ for CP $\Phi$ and arbitrary real $r\le s$. The slack-attainment premises of the decomposition remain explicit.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ThreePieceFilter.lean#L26-L131

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
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
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
# The concrete three-piece filter decomposition

Two hockey-stick filters in the same supplied dilation give the manuscript's
three operators `X`, `W-X`, and `V-W`.  Both their operator-norm bounds and
their complete-positive domination constants are proved here.  The only
filter-existence premises are the explicit slack-attainment propositions.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]

theorem CPLe.smul_nonneg {Φ Ψ : QuantumChannel.T A B}
    (h : CPLe Φ Ψ) {r : ℝ} (hr : 0 ≤ r) : CPLe ((r : ℂ) • Φ) ((r : ℂ) • Ψ) := by
  unfold CPLe at h ⊢
  simpa only [smul_sub] using cp_smul_nonneg h hr

theorem CPLe.add {Φ₁ Φ₂ Ψ₁ Ψ₂ : QuantumChannel.T A B}
    (h₁ : CPLe Φ₁ Ψ₁) (h₂ : CPLe Φ₂ Ψ₂) : CPLe (Φ₁ + Φ₂) (Ψ₁ + Ψ₂) := by
  have h := cp_add h₁ h₂
  have heq : (Ψ₁ - Φ₁) + (Ψ₂ - Φ₂) = (Ψ₁ + Ψ₂) - (Φ₁ + Φ₂) := by abel
  simpa only [CPLe, heq] using h

theorem cp_smul_mono (Φ : QuantumChannel.T A B) (hΦ : IsCompletelyPositive Φ)
    {r s : ℝ} (hrs : r ≤ s) : CPLe ((r : ℂ) • Φ) ((s : ℂ) • Φ) := by
  unfold CPLe
  have heq : (((s - r : ℝ) : ℂ) • Φ) = (s : ℂ) • Φ - (r : ℂ) • Φ := by
    push_cast
    module
  rw [← heq]
  exact cp_smul_nonneg hΦ (sub_nonneg.mpr hrs)

/-- The parallelogram CP bound and two common rate bounds give the factor
four used for both correction and remainder pieces. -/
theorem dilation_difference_four_bound
    (U W : A →ₗ[ℂ] B ⊗[ℂ] E) (M : QuantumChannel.T A B) (r : ℝ)
    (hU : CPLe (dilationChannel U) ((r : ℂ) • M))
    (hW : CPLe (dilationChannel W) ((r : ℂ) • M)) :
    CPLe (dilationChannel (U - W)) (((4 * r : ℝ) : ℂ) • M) := by
  have hsum := (hU.smul_nonneg (r := 2) (by norm_num)).add
    (hW.smul_nonneg (r := 2) (by norm_num))
  simp only [Complex.ofReal_ofNat] at hsum
  have heq : (2 : ℂ) • ((r : ℂ) • M) + (2 : ℂ) • ((r : ℂ) • M) =
      (((4 * r : ℝ) : ℂ) • M) := by
    push_cast
    module
  rw [heq] at hsum
  exact (dilationChannel_sub_le U W).trans hsum

/-- Every supplied dilation of a trace-preserving quantum channel is a contraction. -/
theorem cptp_dilation_norm_le_one (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap) : ‖V.toContinuousLinearMap‖ ≤ 1 := by
  have h := dilation_norm_le_sqrt_of_trace_bound V 1 (by norm_num) (fun a => by
    rw [hV]
    change (Tr (N.toFun (outer_product a a))).re ≤ _
    rw [← N.trace_map, trace_outer_product]
    simp [← Complex.ofReal_pow])
  simpa using h

variable [Nontrivial A] [Nontrivial B]

/-- Actual three-piece dilation decomposition with constants
`(1+b,b+ε,ε)` and CP rates `(γlow,4γhigh,4C)`, where `b` and `ε` are the
square roots of the corresponding concrete hockey-stick divergences.

The low and high filters use the same supplied environment.  This is a
construction of operators, not a hypothesis about the final Schatten bound. -/
theorem hockey_three_piece_decomposition
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (γlow γhigh C : ℝ) (hγlow : 0 ≤ γlow)
    (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M) :
    ∃ X W : A →ₗ[ℂ] B ⊗[ℂ] E,
      X + (W - X) + (V - W) = V ∧
      ‖X.toContinuousLinearMap‖ ≤ 1 + Real.sqrt (channelHockey γlow N M) ∧
      ‖(W - X).toContinuousLinearMap‖ ≤
        Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M) ∧
      ‖(V - W).toContinuousLinearMap‖ ≤ Real.sqrt (channelHockey γhigh N M) ∧
      CPLe (dilationChannel X) ((γlow : ℂ) • M.toLinearMap) ∧
      CPLe (dilationChannel (W - X)) (((4 * γhigh : ℝ) : ℂ) • M.toLinearMap) ∧
      CPLe (dilationChannel (V - W)) (((4 * C : ℝ) : ℂ) • M.toLinearMap) := by
  have hVnorm := cptp_dilation_norm_le_one N V hV
  obtain ⟨X, hXcp, hXerr⟩ := fixed_dilation_hockey_filter_of_slack_attainment
    N M V hγlow hV hlow
  obtain ⟨W, hWcp, hWerr⟩ := fixed_dilation_hockey_filter_of_slack_attainment
    N M V (hγlow.trans hγle) hV hhigh
  have hMcp : IsCompletelyPositive M.toLinearMap := ⟨M.toCompletelyPositiveMap, rfl⟩
  have hXnorm : ‖X.toContinuousLinearMap‖ ≤ 1 + Real.sqrt (channelHockey γlow N M) := by
    have heq : X.toContinuousLinearMap = V.toContinuousLinearMap -
        (V - X).toContinuousLinearMap := by
      ext a
      simp
    rw [heq]
    exact (norm_sub_le V.toContinuousLinearMap (V - X).toContinuousLinearMap).trans
      (add_le_add hVnorm hXerr)
  have hWXnorm : ‖(W - X).toContinuousLinearMap‖ ≤
      Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M) := by
    have heq : (W - X).toContinuousLinearMap =
        (V - X).toContinuousLinearMap - (V - W).toContinuousLinearMap := by
      ext a
      change W a - X a = (V a - X a) - (V a - W a)
      abel
    rw [heq]
    exact (norm_sub_le (V - X).toContinuousLinearMap (V - W).toContinuousLinearMap).trans
      (add_le_add hXerr hWerr)
  have hXhigh : CPLe (dilationChannel X) ((γhigh : ℂ) • M.toLinearMap) :=
    hXcp.trans (cp_smul_mono M.toLinearMap hMcp hγle)
  have hWcap : CPLe (dilationChannel W) ((C : ℂ) • M.toLinearMap) :=
    hWcp.trans (cp_smul_mono M.toLinearMap hMcp hγC)
  have hVcap : CPLe (dilationChannel V) ((C : ℂ) • M.toLinearMap) := by
    simpa only [hV] using hcap
  refine ⟨X, W, ?_, hXnorm, hWXnorm, hWerr, hXcp, ?_, ?_⟩
  · abel
  · exact dilation_difference_four_bound W X M.toLinearMap γhigh hWcp hXhigh
  · exact dilation_difference_four_bound V W M.toLinearMap C hVcap hWcap

end QuantumChannelContinuity


