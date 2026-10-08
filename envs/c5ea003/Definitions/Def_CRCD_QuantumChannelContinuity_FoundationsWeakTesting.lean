-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
-- name    : CRCD_QuantumChannelContinuity_FoundationsWeakTesting
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:10:47.205643+00:00
-- url     : https://prove2.me/theorems/2ade8aae-2ed0-4d97-a3c1-e4edfb96199e
-- title:
--   State relative-entropy bounds for binary testing payoffs
-- statement:
--   For density states on a nonzero finite-dimensional complex Hilbert space, an effect $T$ and a finite relative-entropy bound $D(\rho\|\sigma)\le a$ in bits imply
--
--   $$
--   \ell\operatorname{Tr}(T\rho)-1\le a
--   $$
--
--   whenever the payoff $\operatorname{Tr}(T\rho)-2^\ell\operatorname{Tr}(T\sigma)$ is positive. For $\ell>0$, the effect payoff and the optimized state hockey-stick divergence are each at most $(a+1)/\ell$.
--
--   The binary scalar facts are $p_0\ln p_0+p_1\ln p_1\ge-\ln2$ and, for a binary POVM,
--
--   $$
--   -1-p_0\log_2q_0\le D(\rho\|\sigma).
--   $$
--
--   The entropy inequality uses natural logarithms; relative entropy and the displayed testing bound use base-two logarithms. Measured-outcome expressions use the formal total logarithm at zero, and the divergence comparison is extended-real, so infinite-divergence cases are included.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FoundationsWeakTesting.lean#L20-L104

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




/-! # Concrete Umegaki weak testing bound -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
variable {H : Type} [Qudit H] [Nontrivial H]

/-- The standard binary entropy bound applied to the actual POVM probabilities. -/
theorem binary_entropy_lower (M : POVM H (Fin 2)) (ρ : DensityState H) :
    -Real.log 2 ≤ M.probability ρ 0 * Real.log (M.probability ρ 0) +
      M.probability ρ 1 * Real.log (M.probability ρ 1) := by
  have hsum := M.sum_probability ρ
  rw [Fin.sum_univ_two] at hsum
  have hp1 : 1 - M.probability ρ 0 = M.probability ρ 1 := by linarith
  have h := Real.binEntropy_le_log_two (p := M.probability ρ 0)
  rw [Real.binEntropy, hp1, Real.log_inv, Real.log_inv] at h
  linarith

/-- Binary Umegaki data processing yields the one-outcome testing lower bound,
including singular states and the support-mismatch case. -/
theorem measured_relative_lower (M : POVM H (Fin 2)) (ρ σ : DensityState H) :
    (-1 - M.probability ρ 0 * Real.logb 2 (M.probability σ 0) : ℝ) ≤
      stateRelative ρ σ := by
  by_cases hs : suppLE ρ.op σ.op
  · have hsE := suppLE_of_CPTP M.channel ρ.nonneg σ.nonneg hs
    have hmeas := stateRelative_dataProcessing M.channel ρ σ
    apply le_trans _ hmeas
    rw [umegaki_common_eigenbasis (EuclideanSpace.basisFun (Fin 2) ℂ)
      (ρ.map M.channel) (σ.map M.channel) (M.probability ρ) (M.probability σ)
      (M.channel_apply_basis_probability ρ) (M.channel_apply_basis_probability σ) hsE,
      EReal.coe_le_coe_iff, Fin.sum_univ_two, Real.logb]
    apply (le_div_iff₀ log_two_pos).mpr
    have he := binary_entropy_lower M ρ
    have hq := Real.log_nonpos (M.probability_nonneg σ 1) (M.probability_le_one σ 1)
    have hneg := mul_nonpos_of_nonneg_of_nonpos (M.probability_nonneg ρ 1) hq
    have hcancel : (M.probability ρ 0 * (Real.log (M.probability σ 0) / Real.log 2)) * Real.log 2 =
        M.probability ρ 0 * Real.log (M.probability σ 0) := by
      field_simp [ne_of_gt log_two_pos]
    nlinarith
  · rw [stateRelative_eq_top_of_not_support ρ σ hs]
    exact le_top

/-- The actual binary quantum test supplies the weak-testing logarithmic
inequality required by the manuscript, with no quantum assumptions remaining. -/
theorem binary_relative_testing_log (T : Effect H) (ρ σ : DensityState H)
    {ell a : ℝ} (hD : stateRelative ρ σ ≤ (a : EReal))
    (hpay : 0 < T.probability ρ - (2 : ℝ) ^ ell * T.probability σ) :
    ell * T.probability ρ - 1 ≤ a := by
  let M := binaryPOVM T.op T.nonneg T.le_one
  have hpdef : M.probability ρ 0 = T.probability ρ := by
    simp [M, POVM.probability, Effect.probability, binaryPOVM]
  have hqdef : M.probability σ 0 = T.probability σ := by
    simp [M, POVM.probability, Effect.probability, binaryPOVM]
  have hp : 0 < T.probability ρ := lt_of_le_of_lt
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (T.probability_nonneg σ)) (sub_pos.mp hpay)
  have hs : suppLE ρ.op σ.op := (stateRelative_ne_top_iff ρ σ).mp (by
    intro htop
    rw [htop] at hD
    exact (not_le_of_gt (EReal.coe_lt_top a)) hD)
  have hq : 0 < T.probability σ := by
    rw [← hqdef]
    exact M.probability_pos_of_support ρ σ hs 0 (hpdef.symm ▸ hp)
  have hlog : ell + Real.logb 2 (T.probability σ) ≤ 0 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell) hq)
      ((sub_pos.mp hpay).le.trans (T.probability_le_one ρ))
    rw [Real.logb_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell).ne' hq.ne',
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1), Real.logb_one] at h
    exact h
  have hlow := (measured_relative_lower M ρ σ).trans hD
  rw [EReal.coe_le_coe_iff, hpdef, hqdef] at hlow
  nlinarith

/-- The complete concrete Umegaki weak bound at any strictly positive rate. -/
theorem binary_relative_testing_bound (T : Effect H) (ρ σ : DensityState H)
    {ell a : ℝ} (hell : 0 < ell) (hD : stateRelative ρ σ ≤ (a : EReal)) :
    T.probability ρ - (2 : ℝ) ^ ell * T.probability σ ≤ a / ell + 1 / ell := by
  have ha : 0 ≤ a := EReal.coe_nonneg.mp ((stateRelative_nonneg ρ σ).trans hD)
  have hob : T.probability ρ - (2 : ℝ) ^ ell * T.probability σ ≤ T.probability ρ :=
    sub_le_self _ (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (T.probability_nonneg σ))
  have h := ChannelContinuity.weak_testing_bound_of_positive_payoff
    (n := 1) (r := ell) (d := a) (by norm_num) hell ha hob (fun hpay => by
      simpa using binary_relative_testing_log T ρ σ hD hpay)
  simpa using h

/-- The concrete weak bound passes to the supremum over all acceptance tests. -/
theorem stateHockey_relative_bound (ρ σ : DensityState H) {ell a : ℝ}
    (hell : 0 < ell) (hD : stateRelative ρ σ ≤ (a : EReal)) :
    stateHockey ((2 : ℝ) ^ ell) ρ σ ≤ a / ell + 1 / ell := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T, rfl⟩
  exact binary_relative_testing_bound T ρ σ hell hD

end QuantumChannelContinuity


