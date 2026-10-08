-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
-- name    : CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:12:36.574507+00:00
-- url     : https://prove2.me/theorems/60fdce81-3b08-4469-aa9b-88a407a37098
-- title:
--   The left Rényi limit for states with support mismatch
-- statement:
--   For density states $\rho,\sigma$ on a nonzero finite-dimensional complex Hilbert space, failure of $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ produces an effect $0\le T\le I$ with $\operatorname{Tr}(T\rho)>0$ and $\operatorname{Tr}(T\sigma)=0$. Any such effect implies the extended-real limit
--
--   $$
--   \lim_{\alpha\to1^-}D_\alpha(\rho\|\sigma)=+\infty.
--   $$
--
--   The binary measurement calculation underlying this result is exact. If $q_0=0$, then for $0<\alpha<1$, $Q_\alpha=p_1^\alpha$; if $p_1>0$, its measured divergence is $\frac\alpha{\alpha-1}\log_2p_1$, while $p_1=0$ gives $+\infty$. For $0<p<1$, the scalar expression $\frac\alpha{\alpha-1}\log_2p$ tends to $+\infty$ as $\alpha\to1^-$. The trace identity $\operatorname{Tr}(|v\rangle\langle v|A)=\langle v,Av\rangle$ is also supplied.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FoundationsInfiniteLimit.lean#L25-L180

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
# Infinite left limit from quantum support mismatch

The proof constructs an actual quantum test detecting a kernel witness, then
uses its binary measurement channel and Rényi data processing.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {H : Type} [Qudit H] [Nontrivial H]

/-- Rank-one tests evaluate the Born expectation on their defining vector. -/
theorem trace_outer_mul (v : H) (A : L H) :
    Tr (outer_product v v * A) = inner ℂ v (A v) := by
  have heq : A * outer_product v v = outer_product v (A v) := by
    ext x
    simp [outer_product_eq_rankOne]
  rw [show Tr (outer_product v v * A) = Tr (A * outer_product v v) from
    LinearMap.trace_comp_comm' A (outer_product v v), heq, trace_outer_product]

/-- An actual support mismatch has a normalized rank-one acceptance effect
with zero probability under the denominator and positive probability under
the numerator. -/
theorem exists_test_of_not_support (ρ σ : DensityState H) (hs : ¬ suppLE ρ.op σ.op) :
    ∃ T : Effect H, 0 < T.probability ρ ∧ T.probability σ = 0 := by
  have hex : ∃ x : H, σ.op x = 0 ∧ ρ.op x ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hs
    intro x hx
    exact hn x hx
  obtain ⟨x, hxσ, hxρ⟩ := hex
  have hx : x ≠ 0 := by intro hz; exact hxρ (by simp [hz])
  let v : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hvσ : σ.op v = 0 := by
    change σ.op (((‖x‖⁻¹ : ℝ) : ℂ) • x) = 0
    rw [map_smul, hxσ, smul_zero]
  have hvρ : ρ.op v ≠ 0 := by
    change ρ.op (((‖x‖⁻¹ : ℝ) : ℂ) • x) ≠ 0
    rw [map_smul]
    exact smul_ne_zero (by exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hx)) hxρ
  have hprojection : IsStarProjection (outer_product v v) := by
    rw [outer_product_eq_rankOne, LinearMap.isStarProjection_iff_isSymmetricProjection]
    exact InnerProductSpace.isSymmetricProjection_rankOne_self hv
  let T : Effect H := ⟨outer_product v v, outer_product_self_nonneg v, hprojection.le_one⟩
  refine ⟨T, ?_, ?_⟩
  · change 0 < (Tr (outer_product v v * ρ.op)).re
    rw [trace_outer_mul]
    have hn := ((LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg).re_inner_nonneg_right v
    refine lt_of_le_of_ne hn ?_
    intro hz
    apply hvρ
    apply nonneg_apply_eq_zero_of_inner_self_eq_zero ρ.nonneg
    simpa only [inner_re_symm] using hz.symm
  · change (Tr (outer_product v v * σ.op)).re = 0
    simp [trace_outer_mul, hvσ]

/-- With a zero-probability first outcome in the denominator, the measured
quasi-entropy reduces to a single classical power. -/
theorem measured_quasi_zero_outcome (M : POVM H (Fin 2)) (ρ σ : DensityState H)
    (hq0 : M.probability σ 0 = 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (sandwichedQuasi α (ρ.map M.channel).op (σ.map M.channel).op).re =
      (M.probability ρ 1) ^ α := by
  have hsum := M.sum_probability σ
  rw [Fin.sum_univ_two, hq0, zero_add] at hsum
  have ht : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (sub_pos.mpr hα1).ne'
    (mul_pos (by norm_num) hα0).ne'
  rw [measured_sandwichedQuasi, Fin.sum_univ_two, hq0, hsum]
  simp [Real.zero_rpow ht, Real.zero_rpow hα0.ne']

/-- Exact measured divergence when the remaining numerator probability is
strictly positive. No support-inclusion hypothesis is used. -/
theorem measured_renyi_zero_outcome (M : POVM H (Fin 2)) (ρ σ : DensityState H)
    (hq0 : M.probability σ 0 = 0) (hp1 : 0 < M.probability ρ 1)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    stateRenyi α (ρ.map M.channel) (σ.map M.channel) =
      (α / (α - 1) * Real.logb 2 (M.probability ρ 1) : ℝ) := by
  have hQ := measured_quasi_zero_outcome M ρ σ hq0 hα0 hα1
  have hQne : (sandwichedQuasi α (ρ.map M.channel).op (σ.map M.channel).op).re ≠ 0 := by
    rw [hQ]
    exact (Real.rpow_pos_of_pos hp1 α).ne'
  have hnot : ¬ 1 < α := not_lt.mpr hα1.le
  simp only [stateRenyi, sandwichedRenyiDivNN, hnot, false_and, hQne,
    and_false, or_self, ↓reduceIte, toBits_coe]
  rw [sandwichedRenyiDiv, (ρ.map M.channel).trace_one, hQ]
  simp only [Complex.one_re, div_one]
  rw [Real.log_rpow hp1, Real.logb]
  congr 1
  ring

/-- A perfectly distinguishing binary measurement already has infinite
Rényi divergence for every order between zero and one. -/
theorem measured_renyi_orthogonal (M : POVM H (Fin 2)) (ρ σ : DensityState H)
    (hq0 : M.probability σ 0 = 0) (hp1 : M.probability ρ 1 = 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    stateRenyi α (ρ.map M.channel) (σ.map M.channel) = ⊤ := by
  have hQ := measured_quasi_zero_outcome M ρ σ hq0 hα0 hα1
  rw [hp1, Real.zero_rpow hα0.ne'] at hQ
  unfold stateRenyi sandwichedRenyiDivNN
  rw [if_pos (Or.inr ⟨hα1, (ρ.map M.channel).op_ne_zero, hQ⟩), toBits_top]

/-- The elementary divergence `α log(p)/(α−1)` tends to infinity from below
one whenever `0 < p < 1`. -/
theorem binary_scalar_tendsto_top {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun α : ℝ => ((α / (α - 1) * Real.logb 2 p : ℝ) : EReal))
      (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
  have hc : 0 < -Real.logb 2 p := neg_pos.mpr
    ((Real.logb_neg_iff (by norm_num : (1 : ℝ) < 2) hp).mpr hp1)
  have ht : Tendsto (fun α : ℝ => 1 - α) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : Continuous (fun α : ℝ => (1 : ℝ) - α) := continuous_const.sub continuous_id
      simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact sub_pos.mpr (show α < 1 from hα)
  have hinv := tendsto_inv_nhdsGT_zero.comp ht
  have hbound : Tendsto (fun α : ℝ => (-Real.logb 2 p / 2) * (1 - α)⁻¹)
      (𝓝[<] (1 : ℝ)) atTop := hinv.const_mul_atTop (half_pos hc)
  apply EReal.tendsto_nhds_top_iff_real.mpr
  intro r
  filter_upwards [hbound.eventually (eventually_gt_atTop r), Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with α hr hα
  apply (EReal.coe_lt_coe_iff.mpr hr).trans_le
  apply EReal.coe_le_coe_iff.mpr
  have heq : α / (α - 1) * Real.logb 2 p = α * (-Real.logb 2 p) * (1 - α)⁻¹ := by
    field_simp [ne_of_gt (sub_pos.mpr hα.2), ne_of_lt (sub_neg.mpr hα.2)]
    ring
  change -Real.logb 2 p / 2 * (1 - α)⁻¹ ≤ α / (α - 1) * Real.logb 2 p
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sub_pos.mpr hα.2).le)
  nlinarith [hα.1]

/-- A concrete quantum test with zero denominator acceptance and positive
numerator acceptance forces the full left Rényi limit to infinity. -/
theorem stateRenyi_tendsto_top_left_of_test (ρ σ : DensityState H) (T : Effect H)
    (hp : 0 < T.probability ρ) (hq : T.probability σ = 0) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
  let M := binaryPOVM T.op T.nonneg T.le_one
  have hp0 : 0 < M.probability ρ 0 := by simpa [M, POVM.probability, Effect.probability, binaryPOVM] using hp
  have hq0 : M.probability σ 0 = 0 := by simpa [M, POVM.probability, Effect.probability, binaryPOVM] using hq
  have hsum := M.sum_probability ρ
  rw [Fin.sum_univ_two] at hsum
  have hp1lt : M.probability ρ 1 < 1 := by linarith
  by_cases hp1 : M.probability ρ 1 = 0
  · apply EReal.tendsto_nhds_top_iff_real.mpr
    intro r
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with α hα
    have hd := stateRenyi_dataProcessing M.channel hα.1.le (ne_of_lt hα.2) ρ σ
    rw [measured_renyi_orthogonal M ρ σ hq0 hp1 (lt_trans (by norm_num) hα.1) hα.2] at hd
    exact (EReal.coe_lt_top r).trans_le hd
  · have hp1pos : 0 < M.probability ρ 1 := lt_of_le_of_ne (M.probability_nonneg ρ 1) (Ne.symm hp1)
    have ht := binary_scalar_tendsto_top hp1pos hp1lt
    apply EReal.tendsto_nhds_top_iff_real.mpr
    intro r
    filter_upwards [(EReal.tendsto_nhds_top_iff_real.mp ht) r,
      Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with α hr hα
    apply hr.trans_le
    rw [← measured_renyi_zero_outcome M ρ σ hq0 hp1pos (lt_trans (by norm_num) hα.1) hα.2]
    exact stateRenyi_dataProcessing M.channel hα.1.le (ne_of_lt hα.2) ρ σ

/-- The infinite support-mismatch case of the state-level left limit, with
an actual detecting test constructed from the kernel witness. -/
theorem stateRenyi_tendsto_top_left_of_not_support (ρ σ : DensityState H)
    (hs : ¬ suppLE ρ.op σ.op) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
  obtain ⟨T, hp, hq⟩ := exists_test_of_not_support ρ σ hs
  exact stateRenyi_tendsto_top_left_of_test ρ σ T hp hq

end QuantumChannelContinuity


