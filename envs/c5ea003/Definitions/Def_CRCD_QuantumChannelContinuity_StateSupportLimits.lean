-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
-- name    : CRCD_QuantumChannelContinuity_StateSupportLimits
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:14:50.058815+00:00
-- url     : https://prove2.me/theorems/96eac870-87a6-4cc6-be9b-3cc5f5517160
-- title:
--   Support-filled powers and entropy integrands
-- statement:
--   For a real parameter $s$ and a real scalar $x$, define the continuous extension
--   $$
--   f(s,x)=2(\max(x,0))^{\max(s,3/4)-1/2}\sqrt{\max(x,0)}\log\sqrt{\max(x,0)}.
--   $$
--   It agrees with $x^s\log x$ for $x\ge0$ and $s\ge3/4$, using the total real logarithm convention, and is zero at $x=0$. For a positive operator $A$, the support-filled power is defined by functional calculus from the scalar function that equals $1$ at zero and $x^t$ elsewhere. These objects permit differentiation and convergence on singular spectra without assigning an ordinary inverse on the kernel. The supporting state Rényi limit arguments distinguish support inclusion from support mismatch.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/StateSupportLimits.lean#L22-L394

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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
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






/-! # Order-one limits on the full finite support domain -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set MeasureTheory
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- A globally continuous extension of the integrand `x^s log x` near `s=1`
on the nonnegative half-line. The square-root factor absorbs the logarithm
at zero. -/
noncomputable def supportIntegrand (s x : ℝ) : ℝ :=
  2 * (max x 0) ^ (max s (3 / 4) - 1 / 2) *
    (Real.sqrt (max x 0) * Real.log (Real.sqrt (max x 0)))

theorem continuous_supportIntegrand :
    Continuous (fun p : ℝ × ℝ => supportIntegrand p.1 p.2) := by
  have hb : Continuous (fun p : ℝ × ℝ => max p.2 0) := continuous_snd.max continuous_const
  have he : Continuous (fun p : ℝ × ℝ => max p.1 (3 / 4) - 1 / 2) :=
    (continuous_fst.max continuous_const).sub continuous_const
  have hr : Continuous (fun p : ℝ × ℝ => (max p.2 0) ^ (max p.1 (3 / 4) - 1 / 2)) :=
    hb.rpow he (fun p => Or.inr (by have := le_max_right p.1 (3 / 4 : ℝ); linarith))
  exact (continuous_const.mul hr).mul (Real.continuous_mul_log.comp (Real.continuous_sqrt.comp hb))

theorem supportIntegrand_eq {s x : ℝ} (hs : 3 / 4 ≤ s) (hx : 0 ≤ x) :
    supportIntegrand s x = x ^ s * Real.log x := by
  rw [supportIntegrand, max_eq_left hx, max_eq_left hs]
  by_cases hx0 : x = 0
  · subst x; simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Real.sqrt_eq_rpow, Real.log_rpow hxpos]
    calc
      2 * x ^ (s - 1 / 2) * (x ^ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * Real.log x)) =
          (x ^ (s - 1 / 2) * x ^ (1 / 2 : ℝ)) * Real.log x := by ring
      _ = x ^ s * Real.log x := by rw [← Real.rpow_add hxpos]; congr 2; ring

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Joint continuity of the trace integrand, including singular positive
operators. No continuity of the operator logarithm itself is needed. -/
theorem continuousAt_supportIntegrand_cfc (K : ℝ → L H) {a s₀ : ℝ}
    (hK : ContinuousAt K a) (hKnn : ∀ α, 0 ≤ K α) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Tr (cfc (supportIntegrand p.2) (K p.1))).re) (a, s₀) := by
  let R : ℝ := ‖K a‖ + 1
  let S : Set ℝ := Icc (-R) R
  have hS : IsCompact S := isCompact_Icc
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hf (s : ℝ) : Continuous (supportIntegrand s) :=
    continuous_supportIntegrand.comp (continuous_const.prodMk continuous_id)
  have hfun : Tendsto (fun s : ℝ => UniformOnFun.ofFun {S} (supportIntegrand s))
      (𝓝 s₀) (𝓝 (UniformOnFun.ofFun {S} (supportIntegrand s₀))) := by
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    intro T hT
    have hTS : T = S := Set.mem_singleton_iff.mp hT
    subst T
    change TendstoUniformlyOn (fun s => supportIntegrand s) (supportIntegrand s₀) (𝓝 s₀) S
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    apply Continuous.tendstoUniformly
    exact continuous_supportIntegrand.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hspec {A : L H} (hA : ‖A‖ ≤ R) : spectrum ℝ A ⊆ S := by
    intro x hx
    have hx' : |x| ≤ R := (spectrum.norm_le_norm_of_mem hx).trans hA
    exact abs_le.mp hx'
  have hKbound : ∀ᶠ α in 𝓝 a, ‖K α‖ ≤ R := by
    have ht := hK.norm.eventually (gt_mem_nhds (by dsimp [R]; linarith : ‖K a‖ < R))
    exact ht.mono (fun _ h => h.le)
  have hf1 : ContinuousOn (supportIntegrand s₀) S := (hf s₀).continuousOn
  have hKspec : spectrum ℝ (K a) ⊆ S := hspec (by dsimp [R]; linarith)
  have hcont := (continuousOn_cfc_setProd (A := L H) hS).continuousWithinAt
    (show (UniformOnFun.ofFun {S} (supportIntegrand s₀), K a) ∈
      ({f | ContinuousOn ((UniformOnFun.toFun {S}) f) S} ×ˢ
        {A : L H | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ S}) from
      ⟨hf1, (hKnn a).isSelfAdjoint, hKspec⟩)
  have ht : Tendsto (fun p : ℝ × ℝ =>
      (UniformOnFun.ofFun {S} (supportIntegrand p.2), K p.1)) (𝓝 (a, s₀))
      (𝓝 (UniformOnFun.ofFun {S} (supportIntegrand s₀), K a)) :=
    (hfun.comp continuousAt_snd.tendsto).prodMk_nhds (hK.tendsto.comp continuousAt_fst.tendsto)
  have hmem : ∀ᶠ p : ℝ × ℝ in 𝓝 (a, s₀),
      (UniformOnFun.ofFun {S} (supportIntegrand p.2), K p.1) ∈
        ({f | ContinuousOn ((UniformOnFun.toFun {S}) f) S} ×ˢ
          {A : L H | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ S}) := by
    filter_upwards [continuousAt_fst.tendsto.eventually hKbound] with p hp
    exact ⟨(hf p.2).continuousOn, (hKnn p.1).isSelfAdjoint, hspec hp⟩
  have hwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht hmem
  exact QuantumState.continuous_re_trace.continuousAt.comp
    (hcont.tendsto.comp hwithin)


/-- Spectral trace formula for any scalar function in finite dimension. -/
theorem trace_cfc_real_eq_sum_eigenvalues {A : L H} (hA : 0 ≤ A) (f : ℝ → ℝ) :
    (Tr (cfc f A)).re = ∑ i, f (((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvalues rfl i) := by
  let b := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvectorBasis rfl
  rw [LinearMap.trace_eq_sum_inner (T := cfc f A) b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.apply_eigenvectorBasis rfl i
  have hc := cfc_real_apply_eigenvector hA.isSelfAdjoint f he
    (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) he)
  rw [hc, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re]
  rfl

/-- Fixed-base exponent derivative remains valid at singular positive
operators as long as the exponent is positive. -/
theorem hasDerivAt_trace_rpow_nonneg {A : L H} (hA : 0 ≤ A) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => (Tr (CFC.rpow A t)).re)
      ((Tr (cfc (fun x : ℝ => x ^ s * Real.log x) A)).re) s := by
  have heq (t : ℝ) : CFC.rpow A t = cfc (fun x : ℝ => x ^ t) A := by
    rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real hA
  simp_rw [heq, trace_cfc_real_eq_sum_eigenvalues hA]
  apply HasDerivAt.fun_sum
  intro i _
  let x := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvalues rfl i
  change HasDerivAt (fun t => x ^ t) (x ^ s * Real.log x) s
  have hx : 0 ≤ x := ((LinearMap.nonneg_iff_isPositive A).mp hA).nonneg_eigenvalues rfl i
  by_cases hx0 : x = 0
  · rw [hx0, Real.log_zero, mul_zero]
    apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs] with t ht
    simp [Real.zero_rpow ht.ne']
  · exact (Real.hasStrictDerivAt_const_rpow (lt_of_le_of_ne hx (Ne.symm hx0)) s).hasDerivAt

/-- Spectral expansion as a finite real-linear combination of fixed rank-one
operators; this also handles scalar functions discontinuous at zero. -/
theorem cfc_eq_sum_spectral {A : L H} (hA : 0 ≤ A) (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvalues rfl i) •
      outer_product (((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvectorBasis rfl i)
        (((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvectorBasis rfl i) := by
  classical
  let b := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvectorBasis rfl
  rw [linearMap_eq_sum_outer_product b (cfc f A)]
  apply Finset.sum_congr rfl
  intro i _
  have he := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.apply_eigenvectorBasis rfl i
  have hc := cfc_real_apply_eigenvector hA.isSelfAdjoint f he
    (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) he)
  rw [hc]
  let y := f (((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvalues rfl i)
  have hsmul : (y : ℂ) • outer_product (b i) (b i) = y • outer_product (b i) (b i) :=
    IsScalarTower.algebraMap_smul ℂ y _
  rw [← hsmul]
  ext x
  have hout (u v x : H) : outer_product u v x = inner ℂ u x • v := by
    simp only [outer_product_eq_rankOne, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
  rw [hout, LinearMap.smul_apply, hout]
  change inner ℂ (b i) x • ((y : ℂ) • b i) = (y : ℂ) • (inner ℂ (b i) x • b i)
  exact smul_comm _ _ _

/-- Fill only the zero eigenspace before taking powers. On positive
eigenvalues this is the usual power; on the kernel it is identically one. -/
noncomputable def supportFilledPower (A : L H) (t : ℝ) : L H :=
  cfc (fun x : ℝ => if x = 0 then 1 else x ^ t) A

theorem supportFilledPower_zero {A : L H} (hA : 0 ≤ A) :
    supportFilledPower A 0 = 1 := by
  unfold supportFilledPower
  have hf : (fun x : ℝ => if x = 0 then 1 else x ^ (0 : ℝ)) = fun _ => 1 := by
    funext x; simp
  rw [hf]
  exact cfc_const_one ℝ A (ha := hA.isSelfAdjoint)

theorem hasDerivAt_supportFilledPower_zero {A : L H} (hA : 0 ≤ A) :
    HasDerivAt (supportFilledPower A) (CFC.log A) 0 := by
  unfold supportFilledPower CFC.log
  simp_rw [cfc_eq_sum_spectral hA]
  apply HasDerivAt.fun_sum
  intro i _
  let x := ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric.eigenvalues rfl i
  have hx : 0 ≤ x := ((LinearMap.nonneg_iff_isPositive A).mp hA).nonneg_eigenvalues rfl i
  have hd : HasDerivAt (fun t : ℝ => if x = 0 then 1 else x ^ t) (Real.log x) 0 := by
    by_cases hx0 : x = 0
    · simp only [hx0, ite_true, Real.log_zero]
      exact hasDerivAt_const _ _
    · simp only [hx0, ite_false]
      simpa using (Real.hasStrictDerivAt_const_rpow (lt_of_le_of_ne hx (Ne.symm hx0)) 0).hasDerivAt
  exact hd.smul_const _

/-- A support-compatible numerator removes the artificial kernel filling. -/
theorem supportFilledPower_mul_of_support {ρ σ : L H} (hσ : 0 ≤ σ)
    (hs : suppLE ρ σ) (t : ℝ) :
    ρ * supportFilledPower σ t = ρ * CFC.rpow σ t := by
  classical
  let b := ((LinearMap.nonneg_iff_isPositive σ).mp hσ).isSymmetric.eigenvectorBasis rfl
  apply b.toBasis.ext
  intro i
  let x := ((LinearMap.nonneg_iff_isPositive σ).mp hσ).isSymmetric.eigenvalues rfl i
  have he : σ (b i) = (x : ℂ) • b i :=
    ((LinearMap.nonneg_iff_isPositive σ).mp hσ).isSymmetric.apply_eigenvectorBasis rfl i
  have hc := cfc_real_apply_eigenvector hσ.isSelfAdjoint
    (fun x : ℝ => if x = 0 then 1 else x ^ t) he
    (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) he)
  change ρ (supportFilledPower σ t (b i)) = ρ (CFC.rpow σ t (b i))
  rw [supportFilledPower, hc, rpow_apply_eigenvector hσ t (b.orthonormal.ne_zero i) he]
  simp only [map_smul]
  by_cases hx : x = 0
  · have hk : b i ∈ LinearMap.ker σ := by rw [LinearMap.mem_ker, he, hx]; simp
    have hz : ρ (b i) = 0 := LinearMap.mem_ker.mp (hs hk)
    simp [hx, hz]
  · simp [hx]

/-- The scalar continuous extension agrees with the spectral power-log
integrand throughout the range used by the order-one derivative. -/
theorem cfc_supportIntegrand_eq {A : L H} (hA : 0 ≤ A) {s : ℝ} (hs : 3 / 4 ≤ s) :
    cfc (supportIntegrand s) A = cfc (fun x : ℝ => x ^ s * Real.log x) A := by
  apply cfc_congr
  intro x hx
  exact supportIntegrand_eq hs (spectrum_nonneg_of_nonneg hA hx)

theorem spectrum_real_finite_state (A : L H) : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

theorem rpow_mul_log_eq_cfc {A : L H} (hA : 0 ≤ A) (s : ℝ) :
    CFC.rpow A s * CFC.log A = cfc (fun x : ℝ => x ^ s * Real.log x) A := by
  have he : CFC.rpow A s = cfc (fun x : ℝ => x ^ s) A := by
    rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real hA
  rw [he]
  exact (cfc_mul _ _ A ((spectrum_real_finite_state A).continuousOn _)
    ((spectrum_real_finite_state A).continuousOn _)).symm

theorem continuous_trace_supportIntegrand {A : L H} (hA : 0 ≤ A) :
    Continuous (fun s => (Tr (cfc (supportIntegrand s) A)).re) := by
  simp_rw [trace_cfc_real_eq_sum_eigenvalues hA]
  apply continuous_finset_sum
  intro i _
  exact continuous_supportIntegrand.comp (continuous_id.prodMk continuous_const)

/-- The outer-power contribution has the expected derivative for every
continuous path of nonnegative operators, including paths of singular rank. -/
theorem hasDerivAt_outerPower_nonneg (K : ℝ → L H)
    (hK : ContinuousAt K 1) (hKnn : ∀ α, 0 ≤ K α) :
    HasDerivAt (fun α => (Tr (CFC.rpow (K α) α)).re - (Tr (K α)).re)
      ((Tr (K 1 * CFC.log (K 1))).re) 1 := by
  let g : ℝ → ℝ → ℝ := fun α s => (Tr (cfc (supportIntegrand s) (K α))).re
  have hjoint : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (1, 1) :=
    continuousAt_supportIntegrand_cfc K hK hKnn
  have hint : ∀ α : ℝ, IntervalIntegrable (g α) volume 1 α := by
    intro α
    exact (continuous_trace_supportIntegrand (hKnn α)).intervalIntegrable _ _
  have havg := tendsto_average_of_continuousAt hjoint hint
  have hF : HasDerivAt (fun α => ∫ s in (1 : ℝ)..α, g α s) (g 1 1) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have heq : slope (fun α => ∫ s in (1 : ℝ)..α, g α s) 1 =
        fun α => (α - 1)⁻¹ * ∫ s in (1 : ℝ)..α, g α s := by
      funext α
      rw [slope_def_field, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    rw [heq]
    exact havg
  have hg : g 1 1 = (Tr (K 1 * CFC.log (K 1))).re := by
    dsimp [g]
    rw [cfc_supportIntegrand_eq (hKnn 1) (by norm_num),
      ← rpow_mul_log_eq_cfc (hKnn 1) 1,
      show CFC.rpow (K 1) 1 = K 1 from CFC.rpow_one _ (hKnn 1)]
  rw [hg] at hF
  apply hF.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1)] with α hα
  have hFTC : (∫ s in (1 : ℝ)..α, g α s) =
      (Tr (CFC.rpow (K α) α)).re - (Tr (CFC.rpow (K α) 1)).re := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => (Tr (CFC.rpow (K α) s)).re)
    · intro s hs
      have hs' : 3 / 4 ≤ s := (le_min (by norm_num) hα.le).trans hs.1
      have hd := hasDerivAt_trace_rpow_nonneg (hKnn α) (show 0 < s by linarith)
      simpa only [g, cfc_supportIntegrand_eq (hKnn α) hs'] using hd
    · exact hint α
  simpa only [show CFC.rpow (K α) 1 = K α from CFC.rpow_one _ (hKnn α)] using hFTC.symm

/-- On the support domain, filling the reference kernel has no effect on
the actual sandwiched operator. -/
theorem supportFilledPower_conj_of_support {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hs : suppLE ρ σ) (t : ℝ) :
    supportFilledPower σ t * ρ * supportFilledPower σ t =
      CFC.rpow σ t * ρ * CFC.rpow σ t := by
  have hsa : IsSelfAdjoint (supportFilledPower σ t) := cfc_predicate _ _
  have hpow : IsSelfAdjoint (CFC.rpow σ t) := CFC.rpow_nonneg.isSelfAdjoint
  have hr := supportFilledPower_mul_of_support hσ hs t
  have hl := congrArg star hr
  simp only [star_mul, hρ.isSelfAdjoint.star_eq, hsa.star_eq, hpow.star_eq] at hl
  rw [mul_assoc, hr, ← mul_assoc, hl]

/-- General finite-support derivative of the actual sandwiched quasi-entropy.
Both density operators may be singular and need not commute. -/
theorem hasDerivAt_sandwichedQuasi_one_of_support {ρ σ : L H}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hs : suppLE ρ σ) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      ((Tr (ρ * (CFC.log ρ - CFC.log σ))).re) 1 := by
  let c : ℝ → ℝ := fun α => (1 - α) / (2 * α)
  let P : ℝ → L H := fun α => supportFilledPower σ (c α)
  let K : ℝ → L H := fun α => P α * ρ * P α
  have hc : HasDerivAt c (-(1 / 2 : ℝ)) 1 := by
    have hd := ((hasDerivAt_id (1 : ℝ)).const_sub 1).div
      ((hasDerivAt_id (1 : ℝ)).const_mul 2) (by norm_num)
    convert hd using 1 <;> simp [mul_comm] <;> norm_num
  have hc1 : c 1 = 0 := by norm_num [c]
  have hP : HasDerivAt P ((-(1 / 2 : ℝ)) • CFC.log σ) 1 := by
    have hbase : HasDerivAt (supportFilledPower σ) (CFC.log σ) (c 1) := by
      rw [hc1]; exact hasDerivAt_supportFilledPower_zero hσ
    exact hbase.scomp 1 hc
  have hP1 : P 1 = 1 := by dsimp [P]; rw [hc1, supportFilledPower_zero hσ]
  have hK1 : K 1 = ρ := by simp [K, hP1]
  have hKnn : ∀ α, 0 ≤ K α := by
    intro α
    have hsa : IsSelfAdjoint (P α) := cfc_predicate _ _
    simpa only [hsa.star_eq, K] using star_left_conjugate_nonneg hρ (P α)
  have hD : HasDerivAt K ((-(1 / 2 : ℝ)) •
      (CFC.log σ * ρ + ρ * CFC.log σ)) 1 := by
    convert (hP.mul_const ρ).mul hP using 1
    simp only [hP1, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add]
  have hB : HasDerivAt (fun α => (Tr (K α)).re) (-(Tr (ρ * CFC.log σ)).re) 1 := by
    have hb := hasDerivAt_reTrace_mul_left (1 : L H) hD
    simp only [one_mul] at hb
    convert hb using 1
    have hsc : ((-(1 / 2 : ℝ) : ℝ) : ℂ) • (CFC.log σ * ρ + ρ * CFC.log σ) =
        (-(1 / 2 : ℝ)) • (CFC.log σ * ρ + ρ * CFC.log σ) :=
      IsScalarTower.algebraMap_smul ℂ (-(1 / 2 : ℝ)) (CFC.log σ * ρ + ρ * CFC.log σ)
    rw [← hsc, map_smul, map_add]
    have hcyc : Tr (CFC.log σ * ρ) = Tr (ρ * CFC.log σ) :=
      LinearMap.trace_mul_comm ℂ _ _
    rw [hcyc]
    simp [Complex.real_smul, Complex.add_re]
    <;> ring
  have hA := hasDerivAt_outerPower_nonneg K hD.continuousAt hKnn
  rw [hK1] at hA
  have hadd := hA.add hB
  have heq (α : ℝ) : (sandwichedQuasi α ρ σ).re = (Tr (CFC.rpow (K α) α)).re := by
    unfold sandwichedQuasi
    rw [show K α = CFC.rpow σ (c α) * ρ * CFC.rpow σ (c α) from
      supportFilledPower_conj_of_support hρ hσ hs (c α)]
  convert hadd using 1
  · ext α
    simp only [heq, Pi.add_apply]
    ring
  · rw [mul_sub, map_sub, Complex.sub_re]
    ring

/-- The finite order-one limit for arbitrary support-included density
operators. Singular, noncommuting states are included. -/
theorem stateRenyi_tendsto_one_of_support (ρ σ : DensityState H)
    (hs : suppLE ρ.op σ.op) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) := by
  have hQ1 : (sandwichedQuasi 1 ρ.op σ.op).re = 1 := by
    rw [sandwichedQuasi_one_re ρ.op σ.op σ.nonneg ρ.nonneg, ρ.trace_one]
    rfl
  have hdQ := hasDerivAt_sandwichedQuasi_one_of_support ρ.nonneg σ.nonneg hs
  have hdlog : HasDerivAt (fun α => Real.log ((sandwichedQuasi α ρ.op σ.op).re))
      (umegakiNorm ρ.op σ.op) 1 := by
    simpa [hQ1, umegakiNorm, ρ.trace_one] using
      hdQ.log (by rw [hQ1]; norm_num)
  rw [hasDerivAt_iff_tendsto_slope] at hdlog
  have hreal : Tendsto (fun α => sandwichedRenyiDiv α ρ.op σ.op)
      (𝓝[≠] (1 : ℝ)) (𝓝 (umegakiNorm ρ.op σ.op)) := by
    apply hdlog.congr'
    filter_upwards [] with α
    rw [slope_def_field]
    simp [sandwichedRenyiDiv, hQ1, ρ.trace_one, div_eq_mul_inv, mul_comm]
  have hcoe := (continuous_coe_real_ereal.tendsto
    (umegakiNorm ρ.op σ.op / Real.log 2)).comp (hreal.div_const (Real.log 2))
  have htarget : stateRelative ρ σ = (umegakiNorm ρ.op σ.op / Real.log 2 : ℝ) := by
    simp [stateRelative, umegakiRelEntropyNN, hs]
  rw [htarget]
  apply hcoe.congr'
  have hQne : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), (sandwichedQuasi α ρ.op σ.op).re ≠ 0 :=
    (hdQ.continuousAt.eventually_ne (by rw [hQ1]; norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hQne] with α hα
  simp [stateRenyi, sandwichedRenyiDivNN, hs, hα]

/-- The full two-sided extended-real order-one limit for every pair of
finite-dimensional quantum states, including support mismatch. -/
theorem stateRenyi_tendsto_one {H : Type} [Qudit H] [Nontrivial H] (ρ σ : DensityState H) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) := by
  by_cases hs : suppLE ρ.op σ.op
  · exact stateRenyi_tendsto_one_of_support ρ σ hs
  · rw [stateRelative_eq_top_of_not_support ρ σ hs, ← nhdsLT_sup_nhdsGT]
    apply Filter.Tendsto.sup
    · exact stateRenyi_tendsto_top_left_of_not_support ρ σ hs
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with α hα
      exact (stateRenyi_eq_top_of_not_support hα ρ σ hs).symm



end QuantumChannelContinuity


