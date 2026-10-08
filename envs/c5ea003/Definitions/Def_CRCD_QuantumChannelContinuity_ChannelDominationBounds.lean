-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_ChannelDominationBounds
-- name    : CRCD_QuantumChannelContinuity_ChannelDominationBounds
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:48:42.761841+00:00
-- url     : https://prove2.me/theorems/d152836a-b686-4161-ab09-ad110c771f07
-- title:
--   Uniform channel-divergence bounds from complete-positive domination
-- statement:
--   For CPTP maps $N,M:A\to B$ on nonzero finite-dimensional complex Hilbert spaces, write $N\preceq_{\mathrm{CP}}cM$ when $cM-N$ is completely positive. Such domination implies $c\ge1$, and every stabilized output obeys $(N\otimes\mathrm{id})(\rho)\le c(M\otimes\mathrm{id})(\rho)$. For $c\ge0$, tensor powers satisfy $N^{\otimes n}\preceq_{\mathrm{CP}}c^nM^{\otimes n}$ for every $n\in\mathbb N$.
--
--   With logarithms measured in bits, domination by $c>0$ gives, for every $p>1$,
--
--   $$
--   D_p(N\|M),\ D_p^{\mathrm{reg}}(N\|M)\le \frac p{p-1}\log_2c.
--   $$
--
--   For $c\ge1$, both the one-copy and regularized relative entropies are at most $\log_2c$. These extended-nonnegative divergences are therefore finite. Moreover, there exists a finite real $C_0$ dominating the right threshold $d^+=\inf_{p>1}(D_p^{\mathrm{reg}}(N\|M))_{\mathbb R}$ such that
--
--   $$
--   N^{\otimes n}\preceq_{\mathrm{CP}}2^{n(C_0+1)}M^{\otimes n}\quad(n\in\mathbb N).
--   $$
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/ChannelDominationBounds.lean#L29-L150

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
import Definitions.Def_CRCD_QuantumChannelContinuity_ChoiSupport
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
import Definitions.Def_CRCD_QuantumChannelContinuity_QuantumMain
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_RegularizedExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateDominationBounds
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceExponential
import Definitions.Def_CRCD_QuantumChannelContinuity_ThreePieceFilter
import Definitions.Def_CRCD_QuantumChannelContinuity_TracePowerBounds
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
# Finite channel caps and regularized finiteness

A concrete CP domination constant yields uniform normalized-block bounds for
both divergences. The cap and all finiteness fields are consequences, not
extra quantum hypotheses.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

/-- Trace preservation forces every channel domination constant to be at least one. -/
theorem cp_domination_constant_ge_one (N M : CPTP A B) {c : ℝ}
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) : 1 ≤ c := by
  let ρ := DensityState.maximallyMixed A
  have h := hdom.apply_nonneg ρ.nonneg
  have htr := trace_mul_re_mono h (1 : L B)
    ((LinearMap.nonneg_iff_isPositive _).mp zero_le_one)
  have hN : Tr (N.toLinearMap ρ.op) = 1 := (N.trace_map ρ.op).symm.trans ρ.trace_one
  have hM : Tr (M.toLinearMap ρ.op) = 1 := (M.trace_map ρ.op).symm.trans ρ.trace_one
  simpa only [mul_one, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    Complex.real_smul, hN, hM, Complex.one_re, mul_one] using htr

/-- CP domination holds on every stabilized output with the same constant. -/
theorem cp_domination_amplifiedOutput (N M : CPTP A B) {c : ℝ}
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap))
    (ρ : DensityState (A ⊗[ℂ] A)) :
    (amplifiedOutput N ρ).op ≤ c • (amplifiedOutput M ρ).op := by
  exact (hdom.tensor_identity_scaled (C := A) ⟨N.toCompletelyPositiveMap, rfl⟩).apply_nonneg
    ρ.nonneg

/-- Tensor powers preserve the finite scalar CP bound multiplicatively. -/
theorem channelPower_cp_domination (N M : CPTP A B) {c : ℝ} (hc : 0 ≤ c)
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) (n : ℕ) :
    CPLe (channelPower N n).toLinearMap ((c ^ n) • (channelPower M n).toLinearMap) := by
  induction n with
  | zero =>
    change CPLe (LinearMap.id : T (TensorPower A 0) (TensorPower B 0)) (c ^ 0 • LinearMap.id)
    simp only [pow_zero, one_smul, CPLe, sub_self]
    simpa using cp_smul (cp_identity (C := TensorPower A 0)) (c := 0) le_rfl
  | succ n ih =>
    have h := hdom.tensor_scaled ih ⟨N.toCompletelyPositiveMap, rfl⟩
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩ (pow_nonneg hc n)
    simpa only [channelPower, tensorChannel, pow_succ, mul_comm] using h

/-- An explicit finite bound for every stabilized Rényi divergence above one. -/
theorem channelRenyi_le_of_cp_domination (N M : CPTP A B) {p c : ℝ}
    (hp : 1 < p) (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    channelRenyi p N M ≤ ENNReal.ofReal (p / (p - 1) * Real.logb 2 c) := by
  apply iSup_le
  intro ψ
  exact EReal.toENNReal_le_toENNReal
    (stateRenyi_le_coarse_log_of_le hp hc (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) (cp_domination_amplifiedOutput N M hdom ψ.density))

/-- The normalized block-supremum Rényi divergence is finite at every `p>1`. -/
theorem regularizedRenyi_le_of_cp_domination (N M : CPTP A B) {p c : ℝ}
    (hp : 1 < p) (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRenyi p N M ≤ ENNReal.ofReal (p / (p - 1) * Real.logb 2 c) := by
  refine iSup_le fun n => iSup_le fun hn => ?_
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mpr
  have hb := channelRenyi_le_of_cp_domination (channelPower N n) (channelPower M n)
    hp (pow_pos hc n) (channelPower_cp_domination N M hc.le hdom n)
  rw [Real.logb_pow] at hb
  have heq : p / (p - 1) * ((n : ℝ) * Real.logb 2 c) =
      (p / (p - 1) * Real.logb 2 c) * (n : ℝ) := by ring
  rw [heq, ENNReal.ofReal_mul' (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hb
  exact hb

/-- An explicit finite Umegaki bound on the stabilized channel supremum. -/
theorem channelRelative_le_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 1 ≤ c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    channelRelative N M ≤ ENNReal.ofReal (Real.logb 2 c) := by
  apply iSup_le
  intro ψ
  exact EReal.toENNReal_le_toENNReal
    (stateRelative_le_log_of_le hc (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) (cp_domination_amplifiedOutput N M hdom ψ.density))

/-- Uniform normalized-block Umegaki bound, including every entangled input. -/
theorem regularizedRelative_le_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 1 ≤ c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRelative N M ≤ ENNReal.ofReal (Real.logb 2 c) := by
  refine iSup_le fun n => iSup_le fun hn => ?_
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mpr
  have hb := channelRelative_le_of_cp_domination (channelPower N n) (channelPower M n)
    (one_le_pow₀ hc) (channelPower_cp_domination N M (zero_le_one.trans hc) hdom n)
  rw [Real.logb_pow, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hb
  simpa only [mul_comm] using hb

/-- All finiteness fields of the continuity interface follow from one finite CP bound. -/
theorem regularized_finite_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRelative N M ≠ ⊤ ∧ ∀ p, 1 < p → regularizedRenyi p N M ≠ ⊤ := by
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularizedRelative_le_of_cp_domination N M (cp_domination_constant_ge_one N M hdom) hdom), ?_⟩
  intro p hp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularizedRenyi_le_of_cp_domination N M hp hc hdom)

/-- A completely explicit cap for the threshold and all block domination bounds. -/
theorem finite_cap_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    ∃ cap : ℝ, rightThreshold N M ≤ cap ∧
      ∀ n : ℕ, CPLe (channelPower N n).toLinearMap
        (((2 : ℝ) ^ ((n : ℝ) * (cap + 1))) • (channelPower M n).toLinearMap) := by
  have hc1 := cp_domination_constant_ge_one N M hdom
  have hlog : 0 ≤ Real.logb 2 c := Real.logb_nonneg (by norm_num) hc1
  refine ⟨2 * Real.logb 2 c, ?_, ?_⟩
  · have hth : rightThreshold N M ≤ (regularizedRenyi 2 N M).toReal := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨p, hp, rfl⟩; exact ENNReal.toReal_nonneg⟩
      · exact ⟨2, by norm_num, rfl⟩
    have hb := regularizedRenyi_le_of_cp_domination N M (p := 2) (by norm_num) hc hdom
    norm_num only [sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at hb
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    exact hth.trans hr
  · intro n
    have hb := channelPower_cp_domination N M hc.le hdom n
    have hscale : c ^ n ≤ (2 : ℝ) ^ ((n : ℝ) * (2 * Real.logb 2 c + 1)) := by
      calc
        c ^ n = (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 c) := by
          rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_logb (by norm_num) (by norm_num) hc, Real.rpow_natCast]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
    have hm := cp_smul_mono (channelPower M n).toLinearMap
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩ hscale
    have heq (x : ℝ) : (x : ℂ) • (channelPower M n).toLinearMap =
        x • (channelPower M n).toLinearMap :=
      IsScalarTower.algebraMap_smul ℂ x (channelPower M n).toLinearMap
    simpa only [heq] using hb.trans (by simpa only [heq] using hm)

end QuantumChannelContinuity


