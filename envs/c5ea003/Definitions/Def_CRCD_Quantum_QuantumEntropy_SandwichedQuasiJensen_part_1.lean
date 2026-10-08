-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_1
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:08:37.858747+00:00
-- url     : https://prove2.me/theorems/976e3c64-693e-4a9e-ab0f-e560a4d88cf1
-- title:
--   Positive-cone domains, isometric conjugation, and the right Haar twirl
-- statement:
--   For a nonzero finite-dimensional complex Hilbert space, define the operator interval $\mathcal C_{\varepsilon,M}=\{A:\varepsilon I\le A\le MI\}$ for real $\varepsilon,M$. If $\varepsilon>0$, this set lies in the positive-definite cone. Positive-definite operators admit a positive scalar lower bound, self-adjoint operators admit a scalar upper bound, and the positive semidefinite cone is closed and convex.
--
--   For finite-dimensional spaces $H,H'$ and a linear map $V:H\to H'$, define $C_V(A)=VAV^*$ as a linear map; if $V^*V=I_H$, it is also a continuous non-unital star-algebra homomorphism. For $A\ge0$ and every nonzero real exponent $p$,
--   $$
--   (VAV^*)^p=VA^pV^*.
--   $$
--   Thus $Q_\alpha(V\rho V^*\Vert V\sigma V^*)=Q_\alpha(\rho\Vert\sigma)$ for $\rho,\sigma\ge0$, $\alpha>0$, $\alpha\ne1$, including negative sandwich exponents and singular operators. For $\sigma\ge0$ and $G\ge0$, with arbitrary $\rho$, the variational functional satisfies $V_\alpha(V\rho V^*,V\sigma V^*;G)=V_\alpha(\rho,\sigma;V^*GV)$ under the same order assumptions. These identities do not require surjectivity of $V$.
--
--   For nonzero environment $E$ of dimension $d_E$, normalized Haar measure on its unitary group gives
--   $$
--   \int (I_K\otimes U)X(I_K\otimes U^*)\,dU
--   =\operatorname{Tr}_E(X)\otimes I_E/d_E
--   $$
--   for every operator $X$ on $K\otimes E$, without positivity or trace normalization. The part also proves positivity of $A+\varepsilon I$ for $A\ge0$, $\varepsilon>0$, tensor stability of positive definiteness, finite quasispectra, real-scalar compatibility, continuity of nonnegative operator powers, joint continuity of $\operatorname{Re}Q_\alpha$ on the positive semidefinite cone for $0<\alpha<1$, and joint continuity of $\operatorname{Re}V_\alpha(\cdot,\cdot;G)$ there for $\alpha>1$ and fixed $G\ge0$.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedQuasiJensen.lean#L50-L808

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
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
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
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
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
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Jensen–Haar inequality and monotonicity of the sandwiched Rényi divergence

This file proves the central Jensen-style inequality
(`sandwichedQuasi_jensen_haar`) underlying monotonicity of the sandwiched Rényi
divergence under CPTP maps, and the main monotonicity theorem
(`sandwichedRenyiDiv_monotone`).

The proof is structured in three layers:

1. `jensen_haar_core` — Frank–Lieb's central inequality before tensor
   multiplicativity collapses the LHS / RHS to `Re Q_α(E ρ‖E σ)` and
   `Re Q_α(ρ‖σ)`. Proved by passing to a closed convex sub-cone of `pdSetLM`
   cut out by explicit spectral bounds and applying Mathlib's Bochner-integral
   Jensen (`HaarUnitary.jointly_convex_integral_le` /
   `HaarUnitary.jointly_concave_le_integral`).

2. `sandwichedQuasi_jensen_haar` — the abstract Jensen–Haar interface, obtained
   from `jensen_haar_core` by tensor multiplicativity and the self-quasi
   identity `sandwichedQuasi α τ τ = Tr τ`.

3. `sandwichedRenyiDiv_monotone` — the main theorem
   `D_α(E ρ ‖ E σ) ≤ D_α(ρ ‖ σ)`, obtained from `sandwichedQuasi_jensen_haar`
   by applying the Stinespring dilation (`CPTP.exists_stinespring_dilation`)
   and the monotonic log transform.

The closed sub-cone construction in layer 1 uses
`CFC.exists_pos_algebraMap_le_iff` for the lower bound (positive spectrum gives
`∃ ε > 0, ε • 1 ≤ A`) and operator-norm bounds for the upper bound.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory HaarUnitary TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-- The real scalars act on `L ℋ` compatibly through `ℂ`. This `Prop`-valued
    instance is needed by the `ℝ`-valued (non-unital) functional-calculus
    naturality lemma `NonUnitalStarAlgHomClass.map_cfcₙ`. -/
instance instIsScalarTowerRealComplexL {ℋ : Type u} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (L ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ ℂ r * c) • x = (algebraMap ℝ ℂ r) • (c • x)
    rw [mul_smul]

/-! ### Spectral bounds for operators in `pdSetLM` -/

/-- For any `A ∈ pdSetLM`, there exists a positive real `ε` such that
    `ε • 1 ≤ A.toCLM` in the CLM order. -/
 lemma pdSetLM_exists_pos_lower_bound {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : A ∈ pdSetLM (ℋ := ℋ)) :
    ∃ ε : ℝ, 0 < ε ∧
      (ε • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) ≤
        A.toContinuousLinearMap := by
  obtain ⟨hA_sa, hA_spec⟩ := hA
  obtain ⟨r, hr_pos, hr_le⟩ : ∃ r > 0, algebraMap ℝ (LownerHeinzTheorem.L ℋ) r ≤
      A.toContinuousLinearMap :=
    (CFC.exists_pos_algebraMap_le_iff hA_sa).mpr fun _x hx => hA_spec hx
  refine ⟨r, hr_pos, ?_⟩
  rwa [Algebra.algebraMap_eq_smul_one] at hr_le

/-- For any self-adjoint element `A` in a `CStarAlgebra` of operators on a
    finite-dim Hilbert space, there exists `M` such that `A ≤ M • 1`
    (we may take `M = ‖A‖`). -/
 lemma exists_upper_bound_self_adjoint {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : LownerHeinzTheorem.L ℋ} (hA : IsSelfAdjoint A) :
    ∃ M : ℝ, A ≤ (M • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) := by
  refine ⟨‖A‖, ?_⟩
  rw [show (‖A‖ • (1 : LownerHeinzTheorem.L ℋ) : LownerHeinzTheorem.L ℋ) =
    algebraMap ℝ (LownerHeinzTheorem.L ℋ) ‖A‖ from
      (Algebra.algebraMap_eq_smul_one ‖A‖).symm]
  exact hA.le_algebraMap_norm_self

/-! ### The closed convex sub-cone -/

/-- The closed convex sub-cone of `L ℋ` cut out by `ε • 1 ≤ A ≤ M • 1` (in the
    CLM order, transferred along `toContinuousLinearMap`). -/
 def pdSubCone {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ε M : ℝ) : Set (L ℋ) :=
  {A | ε • (1 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap ∧
       A.toContinuousLinearMap ≤ M • (1 : LownerHeinzTheorem.L ℋ)}











/-- `star (1 ⊗ g) = 1 ⊗ (star g)` for the right tensor factor. -/
 lemma tensorMap_right_star {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (g : L ℋ₂) :
    star (TensorProduct.map (LinearMap.id (M := ℋ₁)) g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star g) := by
  have h_id_sa : star (LinearMap.id : L ℋ₁) = LinearMap.id := by
    rw [show (LinearMap.id : L ℋ₁) = 1 from rfl,
        IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ₁))]
  rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map, ← LinearMap.star_eq_adjoint,
      ← LinearMap.star_eq_adjoint, h_id_sa]

/-- For unitary `u : L ℋ₂`, `TensorProduct.map 1 u` is unitary on `L (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
 lemma tensorMap_right_unitary_of_unitary
    {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    (u : unitary (L ℋ₂)) :
    TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) ∈
      unitary (L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  have h_id_mul_id : (LinearMap.id : L ℋ₁) * LinearMap.id = 1 := mul_one _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · rw [_root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).1]
    exact TensorProduct.map_one
  · rw [_root_.SandwichedRenyiRelativeEntropy.tensorMap_right_star, ← TensorProduct.map_mul, h_id_mul_id,
        (Unitary.mem_iff.mp u.property).2]
    exact TensorProduct.map_one

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is convex. -/
 lemma convex_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    Convex ℝ {A : L 𝒦 | (0 : L 𝒦) ≤ A} := by
  intro a ha b hb θ θ' hθ hθ' _hsum
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  exact add_nonneg (smul_nonneg hθ ha) (smul_nonneg hθ' hb)

/-- The non-negative cone `{A | 0 ≤ A}` in `L 𝒦` is closed (transferred along the
    continuous isometry `toContinuousLinearMap` to the closed positive cone in the
    C⋆-algebra of continuous operators). -/
 lemma isClosed_nonneg_cone {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] :
    IsClosed {A : L 𝒦 | (0 : L 𝒦) ≤ A} := by
  have h_toCLM_cont : Continuous (fun A : L 𝒦 => A.toContinuousLinearMap) :=
    linear_isometry_equiv.continuous
  have h_eq : {A : L 𝒦 | (0 : L 𝒦) ≤ A} =
      (fun A : L 𝒦 => A.toContinuousLinearMap) ⁻¹' (Set.Ici 0) := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rw [LinearMap.nonneg_iff_isPositive, ContinuousLinearMap.nonneg_iff_isPositive,
        LinearMap.isPositive_toContinuousLinearMap_iff]
  rw [h_eq]
  exact isClosed_Ici.preimage h_toCLM_cont



/-- The sub-cone is contained in `pdSetLM` when `ε > 0`. -/
 lemma pdSubCone_subset_pdSetLM {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε M : ℝ} (hε : 0 < ε) : _root_.SandwichedRenyiRelativeEntropy.pdSubCone (ℋ := ℋ) ε M ⊆ pdSetLM (ℋ := ℋ) := by
  intro A ⟨h_lower, _⟩
  -- Use that `ε • 1 = algebraMap ℝ _ ε` and that `algebraMap ε ≤ A.toCLM` gives both
  -- self-adjointness (positivity) and the spectrum bound.
  have h_eq : ε • (1 : LownerHeinzTheorem.L ℋ) = algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [h_eq] at h_lower
  -- `0 ≤ ε • 1` for ε ≥ 0, hence `0 ≤ A.toCLM`.
  have h_pos_1 : (0 : LownerHeinzTheorem.L ℋ) ≤ algebraMap ℝ (LownerHeinzTheorem.L ℋ) ε := by
    have h_one_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ 1 := zero_le_one
    rw [← h_eq]
    exact smul_nonneg hε.le h_one_nn
  have h_A_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    le_trans h_pos_1 h_lower
  have h_A_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_A_nn
  refine ⟨h_A_sa, ?_⟩
  intro r hr
  have h_spec_ge : ∀ x ∈ spectrum ℝ A.toContinuousLinearMap, ε ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ)).mp h_lower
  exact lt_of_lt_of_le hε (h_spec_ge r hr)

/-! ### Helper lemmas for the Form A Jensen–Haar proof -/

/-- **Right-twirl identity** (TrRight analogue of
    `HaarUnitary.twirl_eq_partialTrace_smul_id`).

    For any `X ∈ L(ℋ ⊗ ℋ_env)`,
    `∫ (1 ⊗ u) X (1 ⊗ u*) du = TrRight X ⊗ ((dim ℋ_env)⁻¹ • 1)`,

    where the integral is taken over the normalized Haar measure on
    `unitary (L ℋ_env)`.

    Derived from `twirl_eq_partialTrace_smul_id` by symmetry of the tensor
    factors. The proof composes both sides with `TensorProduct.comm` (or
    equivalently, uses `TrRight = Tr₂ ∘ conjugateEnd (TensorProduct.comm)`). -/
 lemma right_twirl_eq
    {𝒦 : Type u} [Qudit 𝒦]
    {ℋ_env : Type u} [Qudit ℋ_env] [Nontrivial ℋ_env]
    (X : L (𝒦 ⊗[ℂ] ℋ_env)) :
    ∫ u : unitary (L ℋ_env),
        TensorProduct.map (LinearMap.id (M := 𝒦)) ((u : L ℋ_env)) * X *
          TensorProduct.map (LinearMap.id (M := 𝒦)) (star (u : L ℋ_env))
      ∂(HaarUnitary.haarUnitary ℋ_env) =
    TensorProduct.map (QuantumChannel.TrRight X)
      ((Module.finrank ℂ ℋ_env : ℂ)⁻¹ • LinearMap.id (M := ℋ_env)) :=
  HaarUnitary.twirl_eq_partialTrace_right_smul_id X

/-- **Non-unital ⋆-algebra hom** `σ ↦ V σ V*` for an isometric `V` (`V*V = 1`).
    This is multiplicative because of `V*V = 1`, and `*`-preserving in general.
    It is non-unital because `1 ↦ V V* ≠ 1` when `V` is not surjective. -/
 noncomputable def isometricConjHom
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    L ℋ →⋆ₙₐ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    change (V.comp (σ + τ)).comp (LinearMap.adjoint V) =
         (V.comp σ).comp (LinearMap.adjoint V) + (V.comp τ).comp (LinearMap.adjoint V)
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c σ := by
    change (V.comp (c • σ)).comp (LinearMap.adjoint V) =
         c • ((V.comp σ).comp (LinearMap.adjoint V))
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
  map_zero' := by
    change (V.comp 0).comp (LinearMap.adjoint V) = 0
    rw [LinearMap.comp_zero, LinearMap.zero_comp]
  map_mul' σ τ := by
    change (V.comp (σ * τ)).comp (LinearMap.adjoint V) =
         ((V.comp σ).comp (LinearMap.adjoint V)) * ((V.comp τ).comp (LinearMap.adjoint V))
    -- (σ * τ) = σ ∘ₗ τ in `L ℋ`; reduce to function equality.
    ext x
    change V (((σ : L ℋ) * τ) ((LinearMap.adjoint V) x)) =
         V (σ ((LinearMap.adjoint V) (V (τ ((LinearMap.adjoint V) x)))))
    -- (σ * τ) y = σ (τ y); use V.adjoint.comp V = 1.
    have h_id : ∀ y : ℋ, (LinearMap.adjoint V) (V y) = y := fun y => by
      have := LinearMap.congr_fun hV y
      simpa [LinearMap.comp_apply] using this
    change V (σ (τ ((LinearMap.adjoint V) x))) =
         V (σ ((LinearMap.adjoint V) (V (τ ((LinearMap.adjoint V) x)))))
    rw [h_id]
  map_star' σ := by
    change (V.comp (star σ)).comp (LinearMap.adjoint V) =
         star ((V.comp σ).comp (LinearMap.adjoint V))
    rw [show (star σ : L ℋ) = LinearMap.adjoint σ from LinearMap.star_eq_adjoint σ,
        show (star ((V.comp σ).comp (LinearMap.adjoint V)) : L ℋ') =
             LinearMap.adjoint ((V.comp σ).comp (LinearMap.adjoint V)) from
             LinearMap.star_eq_adjoint _,
        LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
        ← LinearMap.comp_assoc]

/-- The isometric-conjugation map `σ ↦ V σ V*` as a *linear* map; this captures the
    underlying linear structure separately from the `NonUnitalStarAlgHom`. -/
 noncomputable def isometricConjLM
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') : L ℋ →ₗ[ℂ] L ℋ' where
  toFun σ := (V.comp σ).comp (LinearMap.adjoint V)
  map_add' σ τ := by
    rw [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c σ := by
    rw [LinearMap.comp_smul, LinearMap.smul_comp]; rfl

/-- Continuity of the isometric-conjugation map (needed to apply `map_cfcₙ`).
    Follows from `continuous_of_finiteDimensional` on the underlying linear map. -/
 lemma isometricConjHom_continuous
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ)) :
    Continuous (_root_.SandwichedRenyiRelativeEntropy.isometricConjHom V hV) := by
  -- The underlying function of isometricConjHom and isometricConjLM are the same.
  have h_coe : (_root_.SandwichedRenyiRelativeEntropy.isometricConjHom V hV : L ℋ → L ℋ') = _root_.SandwichedRenyiRelativeEntropy.isometricConjLM V := rfl
  rw [h_coe]
  exact (_root_.SandwichedRenyiRelativeEntropy.isometricConjLM V).continuous_of_finiteDimensional

/-- The `ℝ`-quasispectrum of any operator on a finite-dimensional qudit is finite:
    `spectrum ℂ a` is finite (`Module.End.finite_spectrum`), `spectrum ℝ a` is its
    preimage under the injective `algebraMap ℝ ℂ`, and the quasispectrum adds only `0`. -/
 lemma quasispectrum_finite {ℋ : Type u} [Qudit ℋ] (a : L ℋ) :
    (quasispectrum ℝ a).Finite := by
  have hC : (spectrum ℂ a).Finite := Module.End.finite_spectrum a
  have hsp : (spectrum ℝ a).Finite := by
    rw [(spectrum.preimage_algebraMap ℂ (a := a)).symm]
    exact hC.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  rw [quasispectrum_eq_spectrum_union_zero]
  exact hsp.union (Set.finite_singleton 0)

/-- **Isometric `rpow` covariance.** For an isometry `V` with `V*V = 1`, a non-negative
    `ω`, and any *nonzero* real `p`: `(V ω V*)^p = V (ω^p) V*`. This is valid even for
    `p < 0`: the function `x ↦ x ^ p` is globally discontinuous at `0`, but the
    quasispectrum of any operator here is finite (so `0` is isolated), hence the function
    is `ContinuousOn` it and the non-unital ⋆-hom naturality `map_cfcₙ` applies. -/
 lemma isometricConj_rpow {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {ω : L ℋ} (hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0) :
    CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
      (V.comp (CFC.rpow ω p)).comp (LinearMap.adjoint V) := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := _root_.SandwichedRenyiRelativeEntropy.isometricConjHom V hV with hφ_def
  have hφ_cont : Continuous φ := _root_.SandwichedRenyiRelativeEntropy.isometricConjHom_continuous V hV
  have hφ_apply : ∀ ν : L ℋ, φ ν = (V.comp ν).comp (LinearMap.adjoint V) := fun _ => rfl
  have hφ_nn : (0 : L ℋ') ≤ φ ω := by
    rw [hφ_apply, LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hω).conj_adjoint V
  let f : ℝ → ℝ := fun x => x ^ p
  have hf_zero : f 0 = 0 := by simp [f, Real.zero_rpow hp]
  have h_Vω_eq : φ ω = (V.comp ω).comp (LinearMap.adjoint V) := hφ_apply ω
  have h_rpow_eq_ω : CFC.rpow ω p = cfc f ω := CFC.rpow_eq_cfc_real (ha := hω)
  have h_rpow_eq_Vω : CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
      cfc f ((V.comp ω).comp (LinearMap.adjoint V)) := by
    have := CFC.rpow_eq_cfc_real (a := φ ω) (y := p) (ha := hφ_nn)
    rw [h_Vω_eq] at this; exact this
  rw [h_rpow_eq_ω, h_rpow_eq_Vω]
  have hcont_ω : ContinuousOn f (quasispectrum ℝ ω) := (_root_.SandwichedRenyiRelativeEntropy.quasispectrum_finite ω).continuousOn _
  have hcont_Vω : ContinuousOn f (quasispectrum ℝ (φ ω)) :=
    (_root_.SandwichedRenyiRelativeEntropy.quasispectrum_finite (φ ω)).continuousOn _
  have h_cfcₙ_eq_ω : cfcₙ f ω = cfc f ω := cfcₙ_eq_cfc hcont_ω hf_zero
  have h_cfcₙ_eq_Vω : cfcₙ f (φ ω) = cfc f (φ ω) := cfcₙ_eq_cfc hcont_Vω hf_zero
  have h_map : φ (cfcₙ f ω) = cfcₙ f (φ ω) :=
    NonUnitalStarAlgHomClass.map_cfcₙ (S := ℂ) φ f ω hcont_ω hf_zero hφ_cont
      (IsSelfAdjoint.of_nonneg hω) (IsSelfAdjoint.of_nonneg hφ_nn)
  change cfc f ((V.comp ω).comp (LinearMap.adjoint V)) =
      (V.comp (cfc f ω)).comp (LinearMap.adjoint V)
  rw [← h_Vω_eq, ← h_cfcₙ_eq_Vω, ← h_map, h_cfcₙ_eq_ω, hφ_apply]

/-- **Isometric invariance of sandwichedQuasi** (valid for all `α > 0`, `α ≠ 1`).

    For an isometry `V : ℋ →ₗ[ℂ] ℋ'` with `V*V = I` and `ρ, σ ≥ 0`,
    `sandwichedQuasi α (V ρ V*) (V σ V*) = sandwichedQuasi α ρ σ`.

    **No convention obstruction in finite dimensions.** Even for `α > 1`, where
    `β = (1 − α) / (2 α) < 0`, the identity still holds: `CFC.rpow (V σ V*) β`
    does *not* collapse to `0`. The function `x ↦ x ^ β` is discontinuous at `0`
    on `ℝ`, but the *quasispectrum* of `V σ V*` is finite (so `0` is an isolated
    point), hence `x ↦ x ^ β` is `ContinuousOn` it and the non-unital ⋆-hom
    naturality `NonUnitalStarAlgHomClass.map_cfcₙ` — which requires only
    `ContinuousOn` over the quasispectrum, not global continuity — applies. The
    result is the support-restricted `V σ^β V*`, exactly as in the `α < 1` case. -/
 lemma sandwichedQuasi_isometric_conj
    {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ')
    (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : (0 : L ℋ) ≤ ρ) (hσ : (0 : L ℋ) ≤ σ) :
    sandwichedQuasi α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) =
      sandwichedQuasi α ρ σ := by
  set φ : L ℋ →⋆ₙₐ[ℂ] L ℋ' := _root_.SandwichedRenyiRelativeEntropy.isometricConjHom V hV with hφ_def
  have hφ_cont : Continuous φ := _root_.SandwichedRenyiRelativeEntropy.isometricConjHom_continuous V hV
  -- φ applied to σ unfolds to (V σ V*).
  have hφ_apply : ∀ ω : L ℋ, φ ω = (V.comp ω).comp (LinearMap.adjoint V) := fun _ => rfl
  -- φ ω ≥ 0 when ω ≥ 0 (positive *-hom).
  have hφ_nn : ∀ {ω : L ℋ}, (0 : L ℋ) ≤ ω → (0 : L ℋ') ≤ φ ω := by
    intro ω hω
    rw [hφ_apply, LinearMap.nonneg_iff_isPositive]
    exact ((LinearMap.nonneg_iff_isPositive _).mp hω).conj_adjoint V
  -- V*V = 1 reduces (V σ V*)(V τ V*) = V (σ τ) V*.
  have h_VV_id : ∀ y : ℋ, (LinearMap.adjoint V) (V y) = y := fun y => by
    have := LinearMap.congr_fun hV y
    simpa [LinearMap.comp_apply] using this
  -- Cyclic trace identity Tr(V X V*) = Tr X.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X := by
    intro X
    have h_assoc : (V.comp X).comp (LinearMap.adjoint V) =
        V.comp (X.comp (LinearMap.adjoint V)) := by
      rw [LinearMap.comp_assoc]
    rw [h_assoc, LinearMap.trace_comp_comm']
    -- Tr ((X ∘ V*) ∘ V) = Tr (X ∘ (V* ∘ V)) = Tr (X ∘ 1) = Tr X
    rw [LinearMap.comp_assoc, hV]
    rfl
  -- Step 1: rpow conjugation `CFC.rpow (V ω V*) p = V (CFC.rpow ω p) V*` for `ω ≥ 0`,
  -- `p ≠ 0` (the extracted `isometricConj_rpow`).
  have h_rpow_conj : ∀ {ω : L ℋ} (_hω : (0 : L ℋ) ≤ ω) {p : ℝ} (hp : p ≠ 0),
      CFC.rpow ((V.comp ω).comp (LinearMap.adjoint V)) p =
        (V.comp (CFC.rpow ω p)).comp (LinearMap.adjoint V) := by
    intro ω hω p hp; exact _root_.SandwichedRenyiRelativeEntropy.isometricConj_rpow V hV hω hp
  -- Now compute the sandwichedQuasi identity.
  unfold sandwichedQuasi
  set β := (1 - α) / (2 * α) with hβ_def
  have hα_pos : 0 < α := hα0
  have hβ_ne : β ≠ 0 := by
    rw [hβ_def]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hα_ne1)) (by positivity)
  -- Step 2: (V σ V*)^β = V (σ^β) V*.
  rw [h_rpow_conj hσ hβ_ne]
  -- Step 3: V (σ^β) V* · V ρ V* · V (σ^β) V* = V (σ^β · ρ · σ^β) V*. Uses V*V = 1.
  have h_inner : (V.comp (CFC.rpow σ β)).comp (LinearMap.adjoint V) *
      (V.comp ρ).comp (LinearMap.adjoint V) *
      (V.comp (CFC.rpow σ β)).comp (LinearMap.adjoint V) =
      (V.comp (CFC.rpow σ β * ρ * CFC.rpow σ β)).comp (LinearMap.adjoint V) := by
    -- Multiplicativity of φ at φ (CFC.rpow σ β), φ ρ, φ (CFC.rpow σ β).
    have hX : φ (CFC.rpow σ β) * φ ρ * φ (CFC.rpow σ β) =
        φ (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
      rw [map_mul φ, map_mul φ]
    simpa [hφ_apply] using hX
  rw [h_inner]
  -- Step 4: (V Y V*)^α = V (Y^α) V* where Y = σ^β · ρ · σ^β ≥ 0, α > 0.
  have h_inner_nn : (0 : L ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β := by
    have hP_nn : (0 : L ℋ) ≤ CFC.rpow σ β := CFC.rpow_nonneg
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg hP_nn
    rw [LinearMap.nonneg_iff_isPositive]
    have hρ_pos := (LinearMap.nonneg_iff_isPositive _).mp hρ
    have := hρ_pos.conj_adjoint (CFC.rpow σ β)
    rw [show LinearMap.adjoint (CFC.rpow σ β) = CFC.rpow σ β from by
        rw [← LinearMap.star_eq_adjoint]; exact hP_sa.star_eq] at this
    -- this : (CFC.rpow σ β ∘ₗ ρ ∘ₗ CFC.rpow σ β).IsPositive
    -- Need: (CFC.rpow σ β * ρ * CFC.rpow σ β).IsPositive
    convert this using 1
  rw [h_rpow_conj h_inner_nn (ne_of_gt hα_pos)]
  -- Step 5: Trace identity Tr (V X V*) = Tr X. Conclude.
  exact h_tr_conj _

/-- **Isometric covariance of the variational functional `quasiVar`** (all `α > 0`,
    `α ≠ 1`). For an isometry `V` (`V*V = 1`), nonneg `σ`, nonneg `G`,
    `quasiVar α (V ρ V*) (V σ V*) G = quasiVar α ρ σ (V* G V)`.

    All `CFC.rpow` exponents appearing (`(α−1)/(2α)` and `α/(α−1)`) are nonzero, so
    `isometricConj_rpow` applies; the inner sandwich identity
    `(V σ^c V*) G (V σ^c V*) = V (σ^c (V* G V) σ^c) V*` is pure associativity. -/
 lemma quasiVar_isometric_conj {ℋ ℋ' : Type u} [Qudit ℋ] [Qudit ℋ']
    (V : ℋ →ₗ[ℂ] ℋ') (hV : (LinearMap.adjoint V).comp V = (1 : L ℋ))
    {α : ℝ} (hα0 : 0 < α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hσ : (0 : L ℋ) ≤ σ) {G : L ℋ'} (hG : (0 : L ℋ') ≤ G) :
    quasiVar α ((V.comp ρ).comp (LinearMap.adjoint V))
        ((V.comp σ).comp (LinearMap.adjoint V)) G =
      quasiVar α ρ σ ((LinearMap.adjoint V).comp (G.comp V)) := by
  set GV : L ℋ := (LinearMap.adjoint V).comp (G.comp V) with hGV_def
  -- exponents
  set c : ℝ := (α - 1) / (2 * α) with hc_def
  set q : ℝ := α / (α - 1) with hq_def
  have hc_ne : c ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα_ne1) (by positivity)
  have hq_ne : q ≠ 0 := div_ne_zero (ne_of_gt hα0) (sub_ne_zero.mpr hα_ne1)
  -- `GV = V* G V ≥ 0` (conjugation of `G ≥ 0` by the adjoint of `V`).
  have hGV_nn : (0 : L ℋ) ≤ GV := by
    rw [hGV_def, LinearMap.nonneg_iff_isPositive]
    have h := ((LinearMap.nonneg_iff_isPositive G).mp hG).conj_adjoint (LinearMap.adjoint V)
    rw [LinearMap.adjoint_adjoint] at h
    exact h
  -- Cyclic trace identity `Tr (V X V*) = Tr X`.
  have h_tr_conj : ∀ X : L ℋ, Tr ((V.comp X).comp (LinearMap.adjoint V)) = Tr X := by
    intro X
    rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hV]; rfl
  -- Term 1: `Tr (G * V ρ V*) = Tr (GV * ρ)`.
  have hterm1 : Tr (G * (V.comp ρ).comp (LinearMap.adjoint V)) = Tr (GV * ρ) := by
    rw [hGV_def,
      show G * (V.comp ρ).comp (LinearMap.adjoint V) =
        ((G.comp V).comp ρ).comp (LinearMap.adjoint V) from by
          simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc],
      LinearMap.trace_comp_comm']
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  -- Inner sandwich identity (pure associativity): `(Vσ^cV*) G (Vσ^cV*) = V (σ^c GV σ^c) V*`.
  have hinner : ((V.comp (CFC.rpow σ c)).comp (LinearMap.adjoint V)) * G *
      ((V.comp (CFC.rpow σ c)).comp (LinearMap.adjoint V)) =
      (V.comp (CFC.rpow σ c * GV * CFC.rpow σ c)).comp (LinearMap.adjoint V) := by
    rw [hGV_def]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  -- `σ^c (V*GV) σ^c ≥ 0` (conjugation of `GV ≥ 0` by self-adjoint `σ^c`).
  have hY_nn : (0 : L ℋ) ≤ CFC.rpow σ c * GV * CFC.rpow σ c := by
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hGV_nn (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  -- Assemble.
  unfold quasiVar
  rw [← hc_def, ← hq_def, _root_.SandwichedRenyiRelativeEntropy.isometricConj_rpow V hV hσ hc_ne, hinner,
      _root_.SandwichedRenyiRelativeEntropy.isometricConj_rpow V hV hY_nn hq_ne, h_tr_conj, hterm1]

/-! ### Positive-definite perturbations `A + ε • 1` (used for the cone arguments) -/

/-- Sum of non-negative and positive-definite is positive-definite. -/
lemma pdSetLM_add_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hB : B ∈ pdSetLM (ℋ := ℋ)) :
    (A + B) ∈ pdSetLM (ℋ := ℋ) := by
  obtain ⟨εB, hεB_pos, hεB_le⟩ := _root_.SandwichedRenyiRelativeEntropy.pdSetLM_exists_pos_lower_bound hB
  have h_A_clm : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) hA
  have hA_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_A_clm
  obtain ⟨MA, hMA_le⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_upper_bound_self_adjoint hA_sa
  obtain ⟨MB, hMB_le⟩ := _root_.SandwichedRenyiRelativeEntropy.exists_upper_bound_self_adjoint hB.1
  have h_toCLM_add : (A + B).toContinuousLinearMap =
      A.toContinuousLinearMap + B.toContinuousLinearMap := by ext x; rfl
  refine _root_.SandwichedRenyiRelativeEntropy.pdSubCone_subset_pdSetLM (ℋ := ℋ) hεB_pos (M := MA + MB) ⟨?_, ?_⟩
  · rw [h_toCLM_add]
    have h_add : εB • (1 : LownerHeinzTheorem.L ℋ) =
        (0 : LownerHeinzTheorem.L ℋ) + εB • (1 : LownerHeinzTheorem.L ℋ) :=
      (zero_add _).symm
    rw [h_add]
    exact add_le_add h_A_clm hεB_le
  · rw [h_toCLM_add]
    have h_sum_eq : (MA + MB) • (1 : LownerHeinzTheorem.L ℋ) =
        MA • (1 : LownerHeinzTheorem.L ℋ) + MB • (1 : LownerHeinzTheorem.L ℋ) :=
      add_smul _ _ _
    rw [h_sum_eq]
    exact add_le_add hMA_le hMB_le

/-- The scalar operator `ε • 1` is positive-definite for `ε > 0` real. -/
lemma pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ε : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) := by
  set τ : L ℋ := (ε : ℂ) • (1 : L ℋ) with hτ_def
  have hε_ne_complex : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hε_nn_complex : (0 : ℂ) ≤ (ε : ℂ) := Complex.zero_le_real.mpr hε.le
  have h_isPos : τ.IsPositive :=
    LinearMap.isPositive_one.smul_of_nonneg hε_nn_complex
  have h_nn : (0 : L ℋ) ≤ τ :=
    (LinearMap.nonneg_iff_isPositive _).mpr h_isPos
  have h_unit : IsUnit τ := by
    refine ⟨⟨τ, ((ε : ℂ))⁻¹ • 1, ?_, ?_⟩, rfl⟩
    · rw [hτ_def, smul_mul_smul_comm, mul_inv_cancel₀ hε_ne_complex, mul_one, one_smul]
    · rw [hτ_def, smul_mul_smul_comm, inv_mul_cancel₀ hε_ne_complex, mul_one, one_smul]
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ τ.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) h_nn
  have h_clm_unit : IsUnit τ.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint τ.toContinuousLinearMap :=
    IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ τ.toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- For non-negative `A` and `ε > 0`, the perturbation `A + ε • 1` is pd. -/
lemma nonneg_add_pos_smul_one_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : L ℋ)) ∈ pdSetLM (ℋ := ℋ) :=
  pdSetLM_add_nonneg hA (pos_smul_one_pdSetLM hε)

/-- From non-negativity and invertibility, conclude positive-definiteness in `pdSetLM`
    (the spectrum is `≥ 0` by positivity and avoids `0` by invertibility). -/
lemma pdSetLM_of_nonneg_isUnit {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (h_nn : (0 : L ℋ) ≤ A) (h_unit : IsUnit A) : A ∈ pdSetLM (ℋ := ℋ) := by
  have h_clm_nn : (0 : LownerHeinzTheorem.L ℋ) ≤ A.toContinuousLinearMap :=
    map_nonneg (toCLMStarAlgHom (ℋ := ℋ)) h_nn
  have h_clm_unit : IsUnit A.toContinuousLinearMap :=
    (toCLMStarAlgHom (ℋ := ℋ)).toRingHom.isUnit_map h_unit
  have h_clm_sa : IsSelfAdjoint A.toContinuousLinearMap := IsSelfAdjoint.of_nonneg h_clm_nn
  refine ⟨h_clm_sa, ?_⟩
  intro r hr
  have h_spec_nn : spectrum ℝ A.toContinuousLinearMap ⊆ Set.Ici 0 :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (ha := h_clm_sa)).1 h_clm_nn
  rcases lt_or_eq_of_le (by simpa [Set.Ici] using h_spec_nn hr) with h | h
  · exact h
  · exfalso; rw [← h] at hr
    exact (spectrum.zero_notMem_iff (R := ℝ)).mpr h_clm_unit hr

/-- The tensor product `A ⊗ B` of two positive-definite operators is positive-definite.
    Non-negativity comes from `A ⊗ B = T * T` with `T = √A ⊗ √B` self-adjoint
    (`T * T = T * T*` is positive); invertibility from the inverse `A⁻¹ ⊗ B⁻¹`. -/
lemma tensorMap_pdSetLM {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    {A : L ℋ₁} {B : L ℋ₂} (hA : A ∈ pdSetLM (ℋ := ℋ₁)) (hB : B ∈ pdSetLM (ℋ := ℋ₂)) :
    TensorProduct.map A B ∈ pdSetLM (ℋ := ℋ₁ ⊗[ℂ] ℋ₂) := by
  haveI : Nontrivial (ℋ₁ ⊗[ℂ] ℋ₂) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  have hA_nn : (0 : L ℋ₁) ≤ A := nonneg_of_pdSetLM hA
  have hB_nn : (0 : L ℋ₂) ≤ B := nonneg_of_pdSetLM hB
  refine pdSetLM_of_nonneg_isUnit ?_ ?_
  · -- Non-negativity: `A ⊗ B = T * T` with `T = √A ⊗ √B` self-adjoint.
    set sA := CFC.sqrt A with hsA
    set sB := CFC.sqrt B with hsB
    have hsA_sa : IsSelfAdjoint sA := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    have hsB_sa : IsSelfAdjoint sB := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
    have hmap : TensorProduct.map A B =
        TensorProduct.map sA sB * TensorProduct.map sA sB := by
      conv_lhs => rw [(CFC.sqrt_mul_sqrt_self A hA_nn).symm, (CFC.sqrt_mul_sqrt_self B hB_nn).symm]
      rw [TensorProduct.map_mul]
    have hT_adj : LinearMap.adjoint (TensorProduct.map sA sB) = TensorProduct.map sA sB := by
      rw [TensorProduct.adjoint_map,
        show LinearMap.adjoint sA = sA from by
          rw [← LinearMap.star_eq_adjoint]; exact hsA_sa.star_eq,
        show LinearMap.adjoint sB = sB from by
          rw [← LinearMap.star_eq_adjoint]; exact hsB_sa.star_eq]
    rw [hmap, LinearMap.nonneg_iff_isPositive]
    have hp := LinearMap.isPositive_self_comp_adjoint (TensorProduct.map sA sB)
    rw [hT_adj] at hp
    exact hp
  · -- Invertibility via the explicit inverse `A⁻¹ ⊗ B⁻¹`.
    obtain ⟨uA, huA⟩ := isUnit_of_pdSetLM hA
    obtain ⟨uB, huB⟩ := isUnit_of_pdSetLM hB
    refine ⟨⟨TensorProduct.map A B,
      TensorProduct.map ((↑uA⁻¹ : L ℋ₁)) ((↑uB⁻¹ : L ℋ₂)), ?_, ?_⟩, rfl⟩
    · rw [← TensorProduct.map_mul, ← huA, ← huB, Units.mul_inv, Units.mul_inv,
        TensorProduct.map_one]
    · rw [← TensorProduct.map_mul, ← huA, ← huB, Units.inv_mul, Units.inv_mul,
        TensorProduct.map_one]

/-! ### Continuity / concavity of `Re Q_α` on the non-negative cone (`α < 1`) -/

/-- For `0 ≤ p`, the map `A ↦ CFC.rpow A p` is continuous on the cone of non-negative
    operators. (A positive power `x ↦ x^p` is continuous up to `0` in `ℝ≥0`, so unlike the
    `pdSetLM` version no spectral gap away from `0` is required.) -/
 lemma rpow_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L 𝒦 => CFC.rpow A p) {A : L 𝒦 | (0 : L 𝒦) ≤ A} :=
  (continuousOn_id (s := {A : L 𝒦 | (0 : L 𝒦) ≤ A})).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem (ha' := fun _ hA => hA)
    (hf := (NNReal.continuous_rpow_const hp).continuousOn)

/-- For `0 < α < 1`, the real part of `sandwichedQuasi` is jointly continuous on the
    non-negative cone. Both exponents `β = (1-α)/(2α)` and `α` are positive, so every
    `CFC.rpow` in the definition is continuous up to the boundary of the cone. -/
 lemma _root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedQuasiJensen_sandwichedQuasi_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) => (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  have hβ_nn : 0 ≤ β := le_of_lt (div_pos (by linarith) (by linarith))
  set S : Set (L 𝒦) := {A : L 𝒦 | (0 : L 𝒦) ≤ A} with hS
  have h_rpow_snd : ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 β) (S ×ˢ S) :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_continuousOn_nonneg hβ_nn).comp continuousOn_snd (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L 𝒦 × L 𝒦 => p.1) (S ×ˢ S) := continuousOn_fst
  have h_inner_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) (S ×ˢ S) :=
    (h_rpow_snd.mul h_fst).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S, (0 : L 𝒦) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β := by
    rintro ⟨ρ, σ⟩ ⟨hρ, _hσ⟩
    have hP_sa : IsSelfAdjoint (CFC.rpow σ β) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hρ (CFC.rpow σ β)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ α))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hα0.le).continuousOn)
  have h_trace_cont : Continuous (fun A : L 𝒦 => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  exact Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)

/-- For `α > 1` and a fixed non-negative `H`, the real part of the variational functional
    `quasiVar α ρ σ H` is jointly continuous on the non-negative cone. The `σ`-exponents
    `(α-1)/(2α)` and `α/(α-1)` are both positive (continuous up to the cone boundary), and
    the `ρ`-term `α (Tr (H ρ))` is linear hence continuous everywhere. -/
 lemma quasiVar_re_continuousOn_nonneg {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {α : ℝ} (hα : 1 < α) {H : L 𝒦} (hH : (0 : L 𝒦) ≤ H) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L 𝒦) => (quasiVar α ρ σ H).re))
      ({A : L 𝒦 | (0 : L 𝒦) ≤ A} ×ˢ {A : L 𝒦 | (0 : L 𝒦) ≤ A}) := by
  set c : ℝ := (α - 1) / (2 * α) with hc
  have hc_nn : 0 ≤ c := le_of_lt (div_pos (by linarith) (by linarith))
  set q : ℝ := α / (α - 1) with hq
  have hq_nn : 0 ≤ q := le_of_lt (div_pos (by linarith) (by linarith))
  set S : Set (L 𝒦) := {A : L 𝒦 | (0 : L 𝒦) ≤ A} with hS
  -- `ρ`-term `(Tr (H * ρ)).re`, continuous everywhere.
  have hTr : Continuous (fun A : L 𝒦 => Tr A) := LinearMap.continuous_of_finiteDimensional _
  have h_rho : Continuous (fun p : L 𝒦 × L 𝒦 => (Tr (H * p.1)).re) :=
    Complex.continuous_re.comp (hTr.comp (continuous_const.mul continuous_fst))
  -- `σ`-term `(Tr ((σ^c H σ^c)^q)).re`, continuous on the cone.
  have h_rpow_snd : ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 c) (S ×ˢ S) :=
    (_root_.SandwichedRenyiRelativeEntropy.rpow_continuousOn_nonneg hc_nn).comp continuousOn_snd (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_inner_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow p.2 c * H * CFC.rpow p.2 c) (S ×ˢ S) :=
    (h_rpow_snd.mul continuousOn_const).mul h_rpow_snd
  have h_inner_nn : ∀ p ∈ S ×ˢ S, (0 : L 𝒦) ≤ CFC.rpow p.2 c * H * CFC.rpow p.2 c := by
    rintro ⟨ρ, σ⟩ _
    have hP_sa : IsSelfAdjoint (CFC.rpow σ c) := IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have h := star_left_conjugate_nonneg hH (CFC.rpow σ c)
    rwa [hP_sa.star_eq] at h
  have h_pow_cont :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 => CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)
        (S ×ˢ S) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ q))
      Filter.univ_mem (ha' := h_inner_nn)
      (hf := (NNReal.continuous_rpow_const hq_nn).continuousOn)
  have h_sigma :
      ContinuousOn (fun p : L 𝒦 × L 𝒦 =>
        (Tr (CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re) (S ×ˢ S) :=
    Complex.continuous_re.comp_continuousOn (hTr.comp_continuousOn h_pow_cont)
  -- Combine: `Re quasiVar = α (Tr Hρ).re − (α−1) (σ-term).re`.
  have h_eq : (Function.uncurry (fun (ρ σ : L 𝒦) => (quasiVar α ρ σ H).re)) =
      fun p : L 𝒦 × L 𝒦 => α * (Tr (H * p.1)).re -
        (α - 1) * (Tr (CFC.rpow (CFC.rpow p.2 c * H * CFC.rpow p.2 c) q)).re := by
    funext p
    obtain ⟨ρ, σ⟩ := p
    change (quasiVar α ρ σ H).re = _
    unfold quasiVar
    rw [← hc, ← hq, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  rw [h_eq]
  exact (continuous_const.mul h_rho).continuousOn.sub (continuousOn_const.mul h_sigma)
end SandwichedRenyiRelativeEntropy


