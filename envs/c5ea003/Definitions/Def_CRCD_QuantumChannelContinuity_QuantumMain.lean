-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_QuantumMain
-- name    : CRCD_QuantumChannelContinuity_QuantumMain
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:45:43.24855+00:00
-- url     : https://prove2.me/theorems/648621f7-a8d9-45ca-a2d7-a1fd6ebcad14
-- title:
--   Finite quantum threshold inputs
-- statement:
--   For channels $N,M$ between nonzero finite-dimensional complex Hilbert spaces, define the real right threshold
--   $$
--   d_+=\inf_{\alpha>1}\bigl(D_\alpha^{\mathrm{reg}}(N\Vert M)\bigr).\mathrm{toReal}.
--   $$
--   The auxiliary `QuantumThresholdInputs` record assumes finite regularized relative entropy, finite regularized Rényi divergences above one, monotonicity there, the relative-to-Rényi lower bound, and a real cap $c\ge d_+$. It also supplies completely positive block domination by $2^{n(c+1)}M_n$, hockey-stick slack attainment for every block and $\gamma\ge1$, and the power-scaling identity for $1<\alpha\le2$ and $n>0$. Its conversion constructs the finite analytic input record and derives the raw Schatten estimate from these supplied fields. Extended-real `toReal` is used inside this finite-branch interface.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/QuantumMain.lean#L27-L133

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_ConcreteMain
import Definitions.Def_CRCD_QuantumChannelContinuity_DilationExistence
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterHockey
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
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
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceExponential
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
# Intermediate continuity interface with the filter–Schatten estimate discharged

This modular interface lists state/order facts, exact CP-slack attainment,
a block CP cap, and scaling under channel powers. The later
`ContinuityAssembly.lean` constructs these inputs from state-order
monotonicity. The regularized three-piece Schatten estimate is derived here.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

noncomputable def rightThreshold (N M : CPTP H K) : ℝ :=
  sInf ((fun α => (regularizedRenyi α N M).toReal) '' Ioi 1)

/-- Concrete inputs for the modular threshold argument. There is no
Schatten, Stinespring, filter-error, tensor-word or raw three-piece field.
`ContinuityAssembly.lean` constructs this record from state-order monotonicity. -/
structure QuantumThresholdInputs (N M : CPTP H K) where
  relative_finite : regularizedRelative N M ≠ ⊤
  renyi_finite : ∀ α, 1 < α → regularizedRenyi α N M ≠ ⊤
  order_mono : MonotoneOn (fun α => (regularizedRenyi α N M).toReal) (Ioi 1)
  relative_le_renyi : ∀ α, 1 < α →
    (regularizedRelative N M).toReal ≤ (regularizedRenyi α N M).toReal
  cap : ℝ
  threshold_le_cap : rightThreshold N M ≤ cap
  block_cap : ∀ n : ℕ, CPLe (channelPower N n).toLinearMap
    (((2 : ℝ) ^ ((n : ℝ) * (cap + 1))) • (channelPower M n).toLinearMap)
  block_slack : ∀ (n : ℕ) (γ : ℝ), 1 ≤ γ →
    HockeySlackAttainment γ (channelPower N n) (channelPower M n)
  power_scaling : ∀ α, 1 < α → α ≤ 2 → ∀ n : ℕ, 0 < n →
    regularizedRenyi α (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRenyi α N M

/-- The infimum threshold is below every admissible order. -/
theorem QuantumThresholdInputs.threshold_le {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) {α : ℝ} (hα : 1 < α) :
    rightThreshold N M ≤ (regularizedRenyi α N M).toReal := by
  apply csInf_le
  · refine ⟨(regularizedRelative N M).toReal, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    exact h.relative_le_renyi β hβ
  · exact ⟨α, hα, rfl⟩

/-- Derivation of the exact raw estimate used by the threshold proof.
All filters and dilations are constructed, and the regularized Schatten bound
is applied to the actual `n`-block channels. -/
theorem QuantumThresholdInputs.raw_schatten {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) (r : ℝ) (hr : 0 ≤ r)
    (hgap : r < rightThreshold N M) (t : ℝ) (ht : 1 ≤ t)
    (n : ℕ) (htn : t < (n : ℝ)) (h2tn : 2 * t ≤ (n : ℝ)) :
    (2 : ℝ) ^ (t * rightThreshold N M / 2) ≤
      ChannelContinuity.rawSchattenRhs n t r (rightThreshold N M) h.cap
        (Real.sqrt (blockTesting N M n r))
        (Real.sqrt (blockTesting N M n (rightThreshold N M + 1 / (t * t)))) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnpos : 0 < (n : ℝ) := htpos.trans htn
  have hn : 0 < n := by exact_mod_cast hnpos
  let p : ℝ := (n : ℝ) / ((n : ℝ) - t)
  have hp : 1 < p := ChannelContinuity.renyi_order_gt_one htpos htn
  have hp2 : p ≤ 2 := ChannelContinuity.renyi_order_le_two htn h2tn
  have hpinv : 1 / p = 1 - t / (n : ℝ) := by
    dsimp [p]
    field_simp
  have hpfrac : (p - 1) / (2 * p) = t / (n : ℝ) / 2 := by
    rw [show (p - 1) / (2 * p) = ((p - 1) / p) / 2 by ring]
    rw [ChannelContinuity.renyi_order_fraction htpos htn]
  let γlow : ℝ := (2 : ℝ) ^ ((n : ℝ) * r)
  let γhigh : ℝ := (2 : ℝ) ^ ((n : ℝ) * (rightThreshold N M + 1 / (t * t)))
  let C : ℝ := (2 : ℝ) ^ ((n : ℝ) * (h.cap + 1))
  have hγlow : 0 ≤ γlow := Real.rpow_nonneg (by norm_num) _
  have hγlow1 : 1 ≤ γlow :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hnpos.le hr)
  have hγle : γlow ≤ γhigh := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    have hi : 0 < 1 / (t * t) := one_div_pos.mpr (mul_pos htpos htpos)
    linarith
  have hγC : γhigh ≤ C := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    have hi : 1 / (t * t) ≤ 1 := (div_le_one (mul_pos htpos htpos)).2 (by nlinarith)
    linarith [h.threshold_le_cap]
  obtain ⟨E, hE, hEne, V, hV⟩ := cptp_has_nontrivial_dilation (channelPower N n)
  letI := hE
  letI := hEne
  have hcap : CPLe (channelPower N n).toLinearMap ((C : ℂ) • (channelPower M n).toLinearMap) := by
    have heq : (C : ℂ) • (channelPower M n).toLinearMap = C • (channelPower M n).toLinearMap :=
      IsScalarTower.algebraMap_smul ℂ C (channelPower M n).toLinearMap
    rw [heq]
    exact h.block_cap n
  have hS := (hockey_three_piece_regularized_exponential
    (channelPower N n) (channelPower M n) V γlow γhigh C hγlow hγle hγC hV hcap
    (h.block_slack n γlow hγlow1) (h.block_slack n γhigh (hγlow1.trans hγle)) hp hp2).2
  rw [h.power_scaling p hp hp2 n hn, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    hpfrac, hpinv] at hS
  have hexp : t / (n : ℝ) / 2 * ((n : ℝ) * (regularizedRenyi p N M).toReal) =
      t * (regularizedRenyi p N M).toReal / 2 := by
    field_simp
  rw [hexp] at hS
  calc
    (2 : ℝ) ^ (t * rightThreshold N M / 2) ≤
        (2 : ℝ) ^ (t * (regularizedRenyi p N M).toReal / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h.threshold_le hp) htpos.le) (by norm_num)
    _ ≤ _ := by
      simpa only [ChannelContinuity.rawSchattenRhs, blockTesting, γlow, γhigh, C] using hS

/-- The old scalar/raw interface is now constructed from precise concrete
quantum premises, using the proved filter–Schatten estimate. -/
noncomputable def QuantumThresholdInputs.toRemaining {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) : RemainingFiniteInputs N M where
  relative_finite := h.relative_finite
  renyi_finite := h.renyi_finite
  order_mono := h.order_mono
  relative_le_renyi := h.relative_le_renyi
  cap := h.cap
  raw_schatten := h.raw_schatten




end QuantumChannelContinuity


