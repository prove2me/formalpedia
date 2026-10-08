-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
-- name    : CRCD_QuantumChannelContinuity_FoundationsTesting
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:53:07.080747+00:00
-- url     : https://prove2.me/theorems/4e77ae8d-bd38-4de8-85ee-6aa76f643c26
-- title:
--   State Rényi testing bounds and measured-outcome lower bounds
-- statement:
--   For density states on a nonzero finite-dimensional complex Hilbert space, let $\alpha>1$, $D_\alpha(\rho\|\sigma)\le a$ in the extended real line, and $0\le T\le I$. Write $p=\operatorname{Re}\operatorname{Tr}(T\rho)$, $q=\operatorname{Re}\operatorname{Tr}(T\sigma)$. If $p-2^\ell q>0$, then
--
--   $$
--   \ell+\frac{\log_2p}{\alpha-1}\le a.
--   $$
--
--   For every real $\ell$, including the nonpositive-payoff case,
--
--   $$
--   p-2^\ell q\le2^{-(\alpha-1)(\ell-a)},\qquad \delta_{2^\ell}(\rho,\sigma)\le2^{-(\alpha-1)(\ell-a)}.
--   $$
--
--   For a finite nonempty POVM and an outcome with $p_i>0$, the bound $\frac\alpha{\alpha-1}\log_2p_i-\log_2q_i\le D_\alpha(\rho\|\sigma)$ uses the formal total logarithm and extended-real divergence. Under support inclusion, $p_i>0$ implies $q_i>0$. For positive scalar probabilities, the sandwiched logarithm is exactly $\frac\alpha{\alpha-1}\log_2p-\log_2q$. All divergence and testing logarithms are in bits.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FoundationsTesting.lean#L20-L139

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





/-! # Concrete quantum Rényi testing bound -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000

 theorem scalar_sandwiched_log {α p q : ℝ}
    (hα : 1 < α) (hp : 0 < p) (hq : 0 < q) :
    (1 / (α - 1)) * Real.logb 2
      ((q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α) =
      (α / (α - 1)) * Real.logb 2 p - Real.logb 2 q := by
  have hqpow : 0 < q ^ ((1 - α) / (2 * α)) := Real.rpow_pos_of_pos hq _
  rw [Real.logb_rpow_eq_mul_logb_of_pos (mul_pos (mul_pos hqpow hp) hqpow),
    Real.logb_mul (ne_of_gt (mul_pos hqpow hp)) hqpow.ne',
    Real.logb_mul hqpow.ne' hp.ne', Real.logb_rpow_eq_mul_logb_of_pos hq]
  field_simp [ne_of_gt (sub_pos.mpr hα), ne_of_gt (lt_trans zero_lt_one hα)]
  ring

variable {H : Type} [Qudit H] [Nontrivial H]

/-- A positive probability on the numerator side forces a positive denominator
probability whenever the quantum support inclusion holds. -/
theorem POVM.probability_pos_of_support {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : POVM H ι) (ρ σ : DensityState H) (hs : suppLE ρ.op σ.op)
    (i : ι) (hp : 0 < M.probability ρ i) : 0 < M.probability σ i := by
  have he := suppLE_of_CPTP M.channel ρ.nonneg σ.nonneg hs
  refine lt_of_le_of_ne (M.probability_nonneg σ i) ?_
  intro hq
  have hz := zero_of_support_common_eigenvector he
    ((EuclideanSpace.basisFun ι ℂ).orthonormal.ne_zero i)
    (M.channel_apply_basis_probability ρ i) (M.channel_apply_basis_probability σ i) hq.symm
  exact hp.ne' hz

/-- The standard single-outcome Rényi testing lower bound, for an arbitrary
POVM applied to the actual density operators. All data processing, diagonal
functional calculus, and support handling are discharged. -/
theorem measured_renyi_lower {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : POVM H ι) (ρ σ : DensityState H) {α : ℝ} (hα : 1 < α)
    (i : ι) (hp : 0 < M.probability ρ i) :
    ((α / (α - 1)) * Real.logb 2 (M.probability ρ i) -
      Real.logb 2 (M.probability σ i) : ℝ) ≤ stateRenyi α ρ σ := by
  by_cases hs : suppLE ρ.op σ.op
  · have hsE := suppLE_of_CPTP M.channel ρ.nonneg σ.nonneg hs
    have hq := M.probability_pos_of_support ρ σ hs i hp
    have hmeas := stateRenyi_dataProcessing M.channel (by linarith : (1 : ℝ) / 2 ≤ α)
      (ne_of_gt hα) ρ σ
    apply le_trans _ hmeas
    rw [stateRenyi_eq_formula hα _ _ hsE, EReal.coe_le_coe_iff,
      measured_sandwichedQuasi M ρ σ α]
    let f : ι → ℝ := fun j => (M.probability σ j ^ ((1 - α) / (2 * α)) *
      M.probability ρ j * M.probability σ j ^ ((1 - α) / (2 * α))) ^ α
    have hfn : ∀ j, 0 ≤ f j := fun j => Real.rpow_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (M.probability_nonneg σ j) _)
        (M.probability_nonneg ρ j)) (Real.rpow_nonneg (M.probability_nonneg σ j) _)) _
    have hqpow : 0 < M.probability σ i ^ ((1 - α) / (2 * α)) := Real.rpow_pos_of_pos hq _
    have hfpos : 0 < f i := Real.rpow_pos_of_pos (mul_pos (mul_pos hqpow hp) hqpow) _
    have hterm : f i ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => hfn j) (Finset.mem_univ i)
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hfpos hterm
    have hmul := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (sub_pos.mpr hα).le)
    rw [_root_.QuantumChannelContinuity.scalar_sandwiched_log hα hp hq] at hmul
    exact hmul
  · rw [stateRenyi_eq_top_of_not_support hα ρ σ hs]
    exact le_top

/-- In the positive-payoff region, the concrete quantum Rényi divergence
bounds the binary testing logarithm needed by the manuscript. -/
theorem binary_renyi_testing_log (M : L H) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (ρ σ : DensityState H) {α ell a : ℝ} (hα : 1 < α)
    (hD : stateRenyi α ρ σ ≤ (a : EReal))
    (hpay : 0 < (Tr (M * ρ.op)).re - (2 : ℝ) ^ ell * (Tr (M * σ.op)).re) :
    ell + (1 / (α - 1)) * Real.logb 2 (Tr (M * ρ.op)).re ≤ a := by
  let B := binaryPOVM M hM hM1
  let p := B.probability ρ 0
  let q := B.probability σ 0
  have hpdef : p = (Tr (M * ρ.op)).re := by simp [p, B, POVM.probability, binaryPOVM]
  have hqdef : q = (Tr (M * σ.op)).re := by simp [q, B, POVM.probability, binaryPOVM]
  have hpay' : 0 < p - (2 : ℝ) ^ ell * q := by rwa [hpdef, hqdef]
  have hp : 0 < p := lt_of_le_of_lt (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (B.probability_nonneg σ 0)) (sub_pos.mp hpay')
  have hs : suppLE ρ.op σ.op := (stateRenyi_ne_top_iff hα ρ σ).mp (by
    intro htop
    rw [htop] at hD
    exact (not_le_of_gt (EReal.coe_lt_top a)) hD)
  have hq : 0 < q := B.probability_pos_of_support ρ σ hs 0 hp
  have hlog : ell + Real.logb 2 q ≤ Real.logb 2 p := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell) hq)
      (sub_pos.mp hpay').le
    rw [Real.logb_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell).ne' hq.ne',
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at h
    exact h
  have hlow := (measured_renyi_lower B ρ σ hα 0 hp).trans hD
  rw [EReal.coe_le_coe_iff] at hlow
  rw [← hpdef]
  change α / (α - 1) * Real.logb 2 p - Real.logb 2 q ≤ a at hlow
  have heq : α / (α - 1) = 1 + 1 / (α - 1) := by
    field_simp [ne_of_gt (sub_pos.mpr hα)]
    ring
  rw [heq] at hlow
  nlinarith

/-- The complete concrete high-rate hockey-stick bound, derived from the
actual CPTP measurement and finite-dimensional quantum Rényi divergence. -/
theorem binary_renyi_testing_bound (M : L H) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (ρ σ : DensityState H) {α ell a : ℝ} (hα : 1 < α)
    (hD : stateRenyi α ρ σ ≤ (a : EReal)) :
    (Tr (M * ρ.op)).re - (2 : ℝ) ^ ell * (Tr (M * σ.op)).re ≤
      (2 : ℝ) ^ (-(α - 1) * (ell - a)) := by
  have hq : 0 ≤ (Tr (M * σ.op)).re := by
    simpa [POVM.probability, binaryPOVM] using
      (binaryPOVM M hM hM1).probability_nonneg σ 0
  have hob : (Tr (M * ρ.op)).re - (2 : ℝ) ^ ell * (Tr (M * σ.op)).re ≤
      (Tr (M * ρ.op)).re := sub_le_self _ (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hq)
  have h := ChannelContinuity.high_testing_bound_of_positive_payoff
    (n := 1) (alpha := α) (a := a) (ell := ell) hα hob (fun hpay => by
      simpa only [one_mul] using binary_renyi_testing_log M hM hM1 ρ σ hα hD hpay)
  simpa using h

/-- The concrete high-rate bound passes to the supremum over every quantum
acceptance effect, with no maximizing effect assumed. -/
theorem stateHockey_renyi_bound (ρ σ : DensityState H) {α ell a : ℝ}
    (hα : 1 < α) (hD : stateRenyi α ρ σ ≤ (a : EReal)) :
    stateHockey ((2 : ℝ) ^ ell) ρ σ ≤ (2 : ℝ) ^ (-(α - 1) * (ell - a)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T, rfl⟩
  exact binary_renyi_testing_bound T.op T.nonneg T.le_one ρ σ hα hD

end QuantumChannelContinuity


