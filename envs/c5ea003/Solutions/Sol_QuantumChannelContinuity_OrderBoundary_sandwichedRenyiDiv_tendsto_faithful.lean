-- Prove2me | solution 1 for QuantumChannelContinuity.OrderBoundary.sandwichedRenyiDiv_tendsto_faithful
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T03:43:00.528279+00:00
-- url     : https://prove2.me/submissions/8bd308f6-aa17-4cf4-989c-4e460c73bd5b

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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CRCD_ChannelContinuity_Testing
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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder

section

/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in LICENSE-MATHLIB.

The spectral faithful-path continuity proofs below are adapted from
Lean-Quantum's SandwichedRenyiNonNeg.lean (pinned dependency bf1c4f6).
They are reproduced because the upstream declarations are private.
-/



/-! # Continuity along faithful density-state approximations -/
open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology NNReal
namespace QuantumChannelContinuity
namespace OrderBoundary
universe u
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private lemma rpow_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L ℋ => CFC.rpow A p) {A : L ℋ | 0 ≤ A} := by
  have h_nhds : (Set.univ : Set ℝ≥0) ∈ 𝓝ˢ (⋃ A ∈ {A : L ℋ | 0 ≤ A}, spectrum ℝ≥0 A) :=
    Filter.univ_mem
  have h_id_cont : ContinuousOn (fun A : L ℋ => A) {A : L ℋ | 0 ≤ A} := continuousOn_id
  have h_nn : ∀ A ∈ {A : L ℋ | 0 ≤ A}, (0 : L ℋ) ≤ A := fun _ hA => hA
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.univ) :=
    NNReal.continuousOn_rpow_const (.inr hp)
  exact h_id_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p))
    h_nhds (ha' := h_nn) (hf := h_f_cont)



private lemma rpow_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (y : ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    CFC.rpow A y v = ((μ ^ y : ℝ) : ℂ) • v := by
  have hsa : IsSelfAdjoint A := (LinearMap.nonneg_iff_isPositive A).mp hA |>.isSelfAdjoint
  have heq : CFC.rpow A y = cfc (fun x : ℝ => x ^ y) A := by
    rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real (ha := hA)
  rw [heq]
  exact cfc_real_apply_eigenvector hsa (fun x => x ^ y) hv hμ

private lemma outer_product_apply {H K : Type u} [Qudit H] [Qudit K]
    (u : H) (v : K) (x : H) : outer_product u v x = inner ℂ u x • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

private noncomputable def outerL {ℋ : Type u} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] L ℋ where
  toFun v := outer_product u v
  map_add' v w := by ext x; simp [_root_.QuantumChannelContinuity.OrderBoundary.outer_product_apply, smul_add]
  map_smul' c v := by
    ext x
    simp only [_root_.QuantumChannelContinuity.OrderBoundary.outer_product_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private lemma continuous_outerL {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => outer_product u v) :=
  (_root_.QuantumChannelContinuity.OrderBoundary.outerL u).continuous_of_finiteDimensional
private lemma sandwichedQuasi_re_ne_zero_of_suppLE
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} (hα : 1 < α)
    {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hs : suppLE ρ σ) (hne : ρ ≠ 0) :
    (sandwichedQuasi α ρ σ).re ≠ 0 :=
  (sandwichedQuasi_pos_of_support (by linarith) ρ σ hρ hσ hs hne).ne'


private lemma rpow_conj_tendsto_faithful
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {A B : L ℋ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupp : suppLE B A)
    {cσ cρ : ℝ} (hcσ : 0 < cσ) (hcρ : 0 ≤ cρ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α))
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow A ((1-α)/(2*α)) * B * CFC.rpow A ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym : A.IsSymmetric := hA_pos.isSymmetric
  have hB_sym : B.IsSymmetric := ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hA_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ):ℂ) • b i := hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → B (b k) = 0 := by
    intro k hk
    exact hsupp (LinearMap.mem_ker.mpr (by rw [h_eig_apply k, hk]; simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (B (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (B (b i)) = inner ℂ (B (b j)) (b i) from (hB_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  -- eigenvalue of the perturbed operator `Pσ λ`.
  set ν : ℝ → Fin n → ℝ := fun lam i => (1-lam)*eig i + lam*cσ with hν
  have hPσ_app : ∀ (lam : ℝ) k,
      (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) (b k) = ((ν lam k : ℝ):ℂ) • b k := by
    intro lam k
    rw [LinearMap.add_apply, LinearMap.smul_apply, h_eig_apply k, LinearMap.smul_apply,
        Module.End.one_apply, smul_smul, ← add_smul, hν]
    push_cast; ring_nf
  have hν_pos : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, 0 < ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    have h2 : 0 < lam*cσ := mul_pos hlam0 hcσ
    rw [hν]; linarith
  have hν_le : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, lam*cσ ≤ ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    rw [hν]; linarith
  -- `A^β (b i) = (eig i)^β • b i`.
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ A :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow A β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => _root_.QuantumChannelContinuity.OrderBoundary.rpow_apply_eigenvector hA β (h_eig_apply i) (hspec0 i)
  have hS0rho : ∀ i, CFC.rpow A β (B (b i))
      = ∑ j, ((((eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hS0b j, smul_smul]
    congr 1; ring
  have hM0 : ∀ i, (CFC.rpow A β * B * CFC.rpow A β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, hS0rho i,
        Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast; ring
  -- per-λ formula for `Pσ^β Pρ Pσ^β (b i)`.
  have hMlam : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ i,
      (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
        * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
        * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i)
      = (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
        + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i := by
    intro lam hlam0 hlam1 i
    set Aε : L ℋ := ((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ) with hAε
    have hAε_nn : (0:L ℋ) ≤ Aε := by
      rw [hAε]
      exact add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hA)
        (smul_nonneg (Complex.zero_le_real.mpr (by positivity)) zero_le_one)
    have hAε_app : ∀ k, Aε (b k) = ((ν lam k : ℝ):ℂ) • b k := hPσ_app lam
    have hAε_spec : ∀ k, ν lam k ∈ spectrum ℝ Aε :=
      fun k => mem_spectrum_real_of_eigenvector (hb_ne k) (hAε_app k)
    have hSb : ∀ k, CFC.rpow Aε β (b k) = (((ν lam k)^β : ℝ):ℂ) • b k :=
      fun k => _root_.QuantumChannelContinuity.OrderBoundary.rpow_apply_eigenvector hAε_nn β (hAε_app k) (hAε_spec k)
    -- expand `(Pρ λ)(b i) = (1-λ)•B(b i) + (λcρ)•b i`.
    have hPρ_app : (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ)) (b i)
        = ((1-lam:ℝ):ℂ) • B (b i) + ((lam*cρ:ℝ):ℂ) • b i := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hSrho : CFC.rpow Aε β (B (b i))
        = ∑ j, ((((ν lam j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
      conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hSb j, smul_smul]
      congr 1; ring
    rw [Module.End.mul_apply, Module.End.mul_apply, hSb i, map_smul, map_smul, hPρ_app,
        map_add, map_smul, map_smul, hSrho, hSb i, smul_add]
    congr 1
    · rw [smul_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      push_cast; ring
    · rw [smul_smul, smul_smul]
      congr 1
      push_cast; ring
  -- `ν lam k → eig k` as `λ → 0⁺`.
  have hν_tendsto : ∀ k, Filter.Tendsto (fun lam : ℝ => ν lam k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun lam : ℝ => ν lam k) := by rw [hν]; fun_prop
    have h0 : Filter.Tendsto (fun lam : ℝ => ν lam k) (nhds 0) (nhds (ν 0 k)) := hcont.tendsto 0
    have : ν 0 k = eig k := by rw [hν]; ring
    rw [this] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hrpow_tendsto : ∀ k, 0 < eig k →
      Filter.Tendsto (fun lam : ℝ => (ν lam k)^β) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig k)^β)) :=
    fun k hk => ((Real.continuousAt_rpow_const (eig k) β (Or.inl (ne_of_gt hk))).tendsto).comp
      (hν_tendsto k)
  -- extra-term scalar `λ·cρ·(ν λ i)^{2β} → 0`.
  have hextra : ∀ i, Filter.Tendsto (fun lam : ℝ => (((lam*cρ * ((ν lam i)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hg : Filter.Tendsto (fun lam : ℝ => cρ * cσ^(2*β) * lam ^ (1/α))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hgc : Filter.Tendsto (fun lam : ℝ => lam ^ (1/α))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h0 := (Real.continuousAt_rpow_const 0 (1/α) (Or.inr hα_inv_pos.le)).tendsto
        rw [Real.zero_rpow (ne_of_gt hα_inv_pos)] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have := hgc.const_mul (cρ * cσ^(2*β))
      simpa using this
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hreal : Filter.Tendsto (fun lam : ℝ => lam*cρ * ((ν lam i)^β)^2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero' (f := fun lam => lam*cρ * ((ν lam i)^β)^2)
        (g := fun lam => cρ * cσ^(2*β) * lam ^ (1/α))
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        exact mul_nonneg (mul_nonneg hlam0.le hcρ) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        have hlam1' : lam ≤ 1 := le_of_lt hlam1
        have hνpos : 0 < ν lam i := hν_pos lam hlam0 hlam1' i
        have hsq : ((ν lam i)^β)^2 = (ν lam i)^(2*β) := by
          rw [← Real.rpow_natCast ((ν lam i)^β) 2, ← Real.rpow_mul hνpos.le]
          ring_nf
        rw [hsq]
        have hlamcσ : 0 < lam*cσ := mul_pos hlam0 hcσ
        have hle : (ν lam i)^(2*β) ≤ (lam*cσ)^(2*β) :=
          Real.rpow_le_rpow_of_nonpos hlamcσ (hν_le lam hlam0 hlam1' i) (by linarith)
        have hlampow : lam * lam^(2*β) = lam ^ (1/α) := by
          rw [← h2β, Real.rpow_add hlam0, Real.rpow_one]
        calc lam*cρ * (ν lam i)^(2*β) ≤ lam*cρ * (lam*cσ)^(2*β) :=
              mul_le_mul_of_nonneg_left hle (mul_nonneg hlam0.le hcρ)
          _ = cρ * cσ^(2*β) * lam ^ (1/α) := by
                rw [Real.mul_rpow hlam0.le hcσ.le, ← hlampow]; ring
      · exact hg
    have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
  -- per-i vector convergence.
  have key : ∀ i, Filter.Tendsto
      (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow A β * B * CFC.rpow A β) (b i))) := by
    intro i
    rw [hM0 i]
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hEq : (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun lam => (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
          + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
      exact hMlam lam hlam (le_of_lt hlam1) i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j) + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · push_neg at hzero
        obtain ⟨hi, hj⟩ := hzero
        have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm hi)
        have hj' : 0 < eig j := lt_of_le_of_ne (h_eig_nn j) (Ne.symm hj)
        have hsc : Filter.Tendsto
            (fun lam : ℝ => ((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
              * inner ℂ (b j) (B (b i)))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i)))) := by
          have hone : Filter.Tendsto (fun lam : ℝ => ((1-lam : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
            have hc : Continuous (fun lam : ℝ => ((1-lam : ℝ):ℂ)) := by fun_prop
            have := hc.tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          have hr : Filter.Tendsto (fun lam : ℝ => (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((eig i)^β * (eig j)^β : ℝ)):ℂ)) :=
            (Complex.continuous_ofReal.tendsto _).comp ((hrpow_tendsto i hi').mul (hrpow_tendsto j hj'))
          have hprod := (hone.mul hr).mul_const (inner ℂ (b j) (B (b i)))
          simpa using hprod
        simpa using hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  -- assemble via outer-product reconstruction.
  have hrecon0 : (CFC.rpow A β * B * CFC.rpow A β)
      = ∑ i, outer_product (b i) ((CFC.rpow A β * B * CFC.rpow A β) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β)
      = (fun lam : ℝ => ∑ i, outer_product (b i)
          ((CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
            * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
            * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))) :=
    funext fun lam => linearMap_eq_sum_outer_product b _
  rw [hrecon0, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((_root_.QuantumChannelContinuity.OrderBoundary.continuous_outerL (b i)).tendsto _).comp (key i)

end OrderBoundary
end QuantumChannelContinuity

open QuantumChannelContinuity QuantumChannelContinuity.OrderBoundary
universe u
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open QuantumChannelContinuity QuantumChannelContinuity.OrderBoundary in
theorem solution
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0)
    (hEsupp : suppLE (E.toFun ρ) (E.toFun σ)) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) := by
  classical
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  set Eρ : L 𝒦 := E.toFun ρ with hEρdef
  set Eσ : L 𝒦 := E.toFun σ with hEσdef
  have hEρ_nn : (0:L 𝒦) ≤ Eρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ_nn : (0:L 𝒦) ≤ Eσ := map_nonneg E.toCompletelyPositiveMap hσ
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  set cσ : ℝ := (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcσ
  set cρ : ℝ := (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcρ
  have hcσ_pos : 0 < cσ := div_pos (trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  have hcρ_nn : 0 ≤ cρ := div_nonneg (le_of_lt (trace_re_pos_of_ne_zero hρ hρ0)) hd_pos.le
  have hEρ0 : Eρ ≠ 0 := by
    intro h
    have hz : (Tr Eρ).re = 0 := by rw [h]; simp
    rw [hEρdef, ← E.trace_map ρ] at hz
    exact (trace_re_pos_of_ne_zero hρ hρ0).ne' hz
  -- Operator convergence along the faithful path (in the target space `𝒦`).
  have hM := _root_.QuantumChannelContinuity.OrderBoundary.rpow_conj_tendsto_faithful (ℋ := 𝒦) hα_gt hEσ_nn hEρ_nn hEsupp hcσ_pos hcρ_nn
  -- Wrap to `sandwichedQuasi` via continuity of `X ↦ Tr (X^α)` on the non-negative cone.
  have hMnn : ∀ X Y : L 𝒦, 0 ≤ Y → (0:L 𝒦) ≤ CFC.rpow X β * Y * CFC.rpow X β :=
    fun X Y hY => conjugate_nonneg_of_nonneg hY CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : L 𝒦 => Tr (CFC.rpow X α)) {X : L 𝒦 | 0 ≤ X}
      (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) := by
    have h1 : ContinuousOn (fun X : L 𝒦 => CFC.rpow X α) {X : L 𝒦 | 0 ≤ X} :=
      _root_.QuantumChannelContinuity.OrderBoundary.rpow_continuousOn_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : L 𝒦 => Tr A) := LinearMap.continuous_of_finiteDimensional _
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn Eσ Eρ hEρ_nn)
  have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have hMwithin : Filter.Tendsto
      (fun lam : ℝ => CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β
        * (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        * CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) {X : L 𝒦 | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    have hlam0 : (0:ℝ) < lam := hlam
    have hlam1' : lam < 1 := hlam1
    have hPρ_nn : (0:L 𝒦) ≤ ((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hEρ_nn)
        (smul_nonneg (Complex.zero_le_real.mpr (mul_nonneg hlam0.le hcρ_nn)) zero_le_one)
    exact hMnn _ _ hPρ_nn
  have hQcx := Filter.Tendsto.comp hcont hMwithin
  -- `sandwichedRenyiDiv` tendsto over the real parameter `λ`.
  have hTr0 : (Tr Eρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ_nn hEρ0)
  have hQ0 : (sandwichedQuasi α Eρ Eσ).re ≠ 0 :=
    _root_.QuantumChannelContinuity.OrderBoundary.sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hEρ_nn hEσ_nn hEsupp hEρ0
  have hQre : Filter.Tendsto
      (fun lam : ℝ => (sandwichedQuasi α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α Eρ Eσ).re) :=
    (Complex.continuous_re.tendsto _).comp hQcx
  have hTre : Filter.Tendsto
      (fun lam : ℝ => (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr Eρ).re) := by
    have hform : ∀ lam : ℝ, (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re
        = (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ) := by
      intro lam
      rw [map_add, map_smul, map_smul, LinearMap.trace_one, smul_eq_mul, smul_eq_mul,
          Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.natCast_re]
    simp_rw [hform]
    have hcont : Continuous
        (fun lam : ℝ => (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ)) := by
      fun_prop
    have h2 := hcont.tendsto 0
    have h3 : (1-(0:ℝ)) * (Tr Eρ).re + (0*cρ) * (Module.finrank ℂ 𝒦 : ℝ) = (Tr Eρ).re := by ring
    rw [h3] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hD : Filter.Tendsto
      (fun lam : ℝ => sandwichedRenyiDiv α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedRenyiDiv α Eρ Eσ)) := by
    unfold sandwichedRenyiDiv
    have hRatio := Filter.Tendsto.div hQre hTre hTr0
    exact ((Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio).const_mul _
  -- Transfer to the subtype filter; identify `F_λ.toFun` with the explicit perturbation.
  have hFeq : ∀ (X : L ℋ) (cX : ℝ), cX = (Tr X).re / (Module.finrank ℂ 𝒦 : ℝ) → 0 ≤ X →
      ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        (faithfulApprox E l.val l.property.1.le l.property.2).toFun X
          = ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val*cX:ℝ):ℂ)•(1:L 𝒦) := by
    intro X cX hcX hX l
    have hTrX_re : Tr X = ((Tr X).re : ℂ) := by
      have h := ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
      rw [Complex.le_def] at h
      exact (Complex.ext rfl h.2.symm)
    change ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val:ℝ):ℂ)•((Tr X/(Module.finrank ℂ 𝒦:ℂ))•(1:L 𝒦)) = _
    rw [smul_smul]
    congr 2
    rw [hTrX_re, hcX]
    push_cast
    field_simp
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htc : Filter.Tendsto (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin 0 (Set.Ioi 0)) := Filter.tendsto_comap
  have hcomp := hD.comp htc
  refine hcomp.congr' ?_
  filter_upwards with l
  rw [Function.comp_apply, hFeq ρ cρ hcρ hρ l, hFeq σ cσ hcσ hσ l]

end
