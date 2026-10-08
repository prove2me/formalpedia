-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
-- name    : CRCD_Quantum_QuantumEntropy_HaarUnitary
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:44:41.442315+00:00
-- url     : https://prove2.me/theorems/097619d2-a43e-415d-a305-8153f814eeaa
-- title:
--   Normalized Haar measure and unitary-group auxiliary maps
-- statement:
--   Let $H$ be a nonzero finite-dimensional complex Hilbert space. The endomorphism algebra carries its operator-norm topology, transported from continuous linear maps, with continuous multiplication and adjoint. Its unitary group $U(H)$ is compact and locally compact. Taking the whole compact group as the normalizing positive compact set defines a probability Haar measure $\mu_H$ with
--
--   $$\mu_H(U(H))=1,\qquad \mu_H(gS)=\mu_H(S)\quad(g\in U(H)),$$
--
--   for measurable $S$. The endomorphism algebra is equipped with the Borel measurable structure corresponding to that topology. Auxiliary finite-dimensional maps include the rank-one operator and its associated reflection expression,
--
--   $$P_v(x)=\langle v,x\rangle v,\qquad R_v=I-2P_v.$$
--
--   These formulas are defined for every $v\in H$; $P_v$ is a projection and $R_v$ a unitary reflection when $\|v\|=1$. This interface provides the measure and operator topology needed for averaging unitary conjugations in the data-processing argument.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/HaarUnitary.lean#L61-L830

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
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



-- Haar measure on locally compact groups

-- IsTopologicalGroup instance for unitary groups

-- Jensen's inequality for convex/concave functions under probability measures

-- Haar-invariant integrals (integral_mul_left_eq_self)

-- Trace of rank-one operators and inner product

-- finrank_eq_card_basis

-- IsCentral for End, center of endomorphism algebras

-- rTensorStarAlgHom, lTensorStarAlgHom, map_eq_rTensor_mul_lTensor


/-!
# Haar measure on the unitary group and tools for Theorem 1

Infrastructure for the normalized (probability) Haar measure on the finite-dimensional
unitary group, the twirl identity, and Jensen-type inequalities for jointly convex /
concave operator functions under Haar integration.

These are the measure-theoretic ingredients needed to derive monotonicity of the
sandwiched Rényi relative entropy (Theorem 1 of Frank–Lieb, arXiv:1306.5358) from
Proposition 3 (joint convexity / concavity of the sandwiched quasi-relative entropy).

## Convention

We write `Tr₂` for `QuantumChannel.Tr₂`, which traces out the **first** tensor factor:
  `Tr₂ : L(ℋ₁ ⊗ ℋ₂) → L ℋ₂`.
When the first factor is the "environment" ℋ_env and the second is the main system ℋ,
`Tr₂` computes the partial trace over the environment. This matches the Stinespring
convention `E(γ) = Tr₂(U (τ ⊗ γ) U*)` where τ is the environment state on ℋ₁ and
γ is the input state on ℋ₂.
-/

open QuantumState QuantumChannel TensorCFC
open MeasureTheory MeasureTheory.Measure
open GeneralizedPerspectiveFunction
open scoped ComplexOrder TensorProduct

namespace HaarUnitary

universe u

/-! ## Section 1: Compactness of the unitary group and Haar measure -/

section CompactHaar

variable {ℋ : Type u} [Qudit ℋ]

noncomputable instance instMeasurableSpaceLM : MeasurableSpace (L ℋ) := borel (L ℋ)
instance instBorelSpaceLM : BorelSpace (L ℋ) := ⟨rfl⟩

-- Topology on `L ℋ` induced from CLM is compatible with multiplication and star
 noncomputable abbrev iso (ℋ : Type u) [Qudit ℋ] := linear_isometry_equiv (ℋ := ℋ)



 lemma iso_mul (a b : L ℋ) : _root_.HaarUnitary.iso ℋ (a * b) = _root_.HaarUnitary.iso ℋ a * _root_.HaarUnitary.iso ℋ b := by
  change LinearMap.toContinuousLinearMap (a * b) =
    LinearMap.toContinuousLinearMap a * LinearMap.toContinuousLinearMap b
  exact (Module.End.toContinuousLinearMap ℋ).map_mul a b

 lemma iso_star (a : L ℋ) : _root_.HaarUnitary.iso ℋ (star a) = star (_root_.HaarUnitary.iso ℋ a) := by
  change LinearMap.toContinuousLinearMap (star a) = star (LinearMap.toContinuousLinearMap a)
  ext x; rfl

noncomputable instance instContinuousMulLM : ContinuousMul (L ℋ) where
  continuous_mul := by
    suffices h : ∀ a b : L ℋ, a * b = (_root_.HaarUnitary.iso ℋ).symm ((_root_.HaarUnitary.iso ℋ) a * (_root_.HaarUnitary.iso ℋ) b) by
      simp_rw [h]
      exact (_root_.HaarUnitary.iso ℋ).symm.continuous.comp
        (continuous_mul.comp ((_root_.HaarUnitary.iso ℋ).continuous.prodMap (_root_.HaarUnitary.iso ℋ).continuous))
    intro a b
    conv_rhs => rw [show (_root_.HaarUnitary.iso ℋ) a * (_root_.HaarUnitary.iso ℋ) b = (_root_.HaarUnitary.iso ℋ) (a * b) from (_root_.HaarUnitary.iso_mul a b).symm]
    exact ((_root_.HaarUnitary.iso ℋ).symm_apply_apply (a * b)).symm

noncomputable instance instContinuousStarLM : ContinuousStar (L ℋ) where
  continuous_star := by
    suffices h : (star : L ℋ → L ℋ) = (_root_.HaarUnitary.iso ℋ).symm ∘ star ∘ (_root_.HaarUnitary.iso ℋ) by
      rw [h]
      exact (_root_.HaarUnitary.iso ℋ).symm.continuous.comp (continuous_star.comp (_root_.HaarUnitary.iso ℋ).continuous)
    funext a
    change star a = (_root_.HaarUnitary.iso ℋ).symm (star ((_root_.HaarUnitary.iso ℋ) a))
    conv_rhs => rw [show star ((_root_.HaarUnitary.iso ℋ) a) = (_root_.HaarUnitary.iso ℋ) (star a) from (_root_.HaarUnitary.iso_star a).symm]
    exact ((_root_.HaarUnitary.iso ℋ).symm_apply_apply (star a)).symm

/-- Every unitary operator on a finite-dimensional Hilbert space has operator norm ≤ 1. -/
lemma unitaryNormBound [Nontrivial ℋ] (U : unitary (L ℋ)) : ‖(U : L ℋ)‖ ≤ 1 := by
  rw [CStarRing.norm_coe_unitary]

/-- The unitary group on a finite-dimensional Hilbert space is bounded. -/
lemma unitary_isBounded [Nontrivial ℋ] : Bornology.IsBounded (unitary (L ℋ) : Set (L ℋ)) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  exact ⟨2, fun x hx => by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (unitaryNormBound ⟨x, hx⟩) one_lt_two⟩

/-- The unitary group on a finite-dimensional Hilbert space is compact
    (closed + bounded in a finite-dimensional normed space). -/
instance compactSpace_unitary [Nontrivial ℋ] : CompactSpace (unitary (L ℋ)) := by
  have : ProperSpace (L ℋ) := FiniteDimensional.proper ℂ (L ℋ)
  exact isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_unitary unitary_isBounded)

instance locallyCompactSpace_unitary [Nontrivial ℋ] : LocallyCompactSpace (unitary (L ℋ)) := by
  haveI : ProperSpace (unitary (L ℋ)) := proper_of_compact
  exact locallyCompact_of_proper

 noncomputable def unitaryPC (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    TopologicalSpace.PositiveCompacts (unitary (L ℋ)) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

/-- The normalized (probability) Haar measure on the unitary group of `L ℋ`.
    Normalized so that `haarUnitary ℋ Set.univ = 1`, making it a probability measure. -/
noncomputable def haarUnitary (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    Measure (unitary (L ℋ)) :=
  haarMeasure (_root_.HaarUnitary.unitaryPC ℋ)

instance haarUnitary_isHaarMeasure [Nontrivial ℋ] :
    IsHaarMeasure (haarUnitary ℋ) := by
  unfold haarUnitary; infer_instance

/-- `haarUnitary` is a probability measure on a compact group. -/
instance haarUnitary_isProbabilityMeasure [Nontrivial ℋ] :
    IsProbabilityMeasure (haarUnitary ℋ) :=
  ⟨by change haarMeasure (_root_.HaarUnitary.unitaryPC ℋ) Set.univ = 1
      have : haarMeasure (_root_.HaarUnitary.unitaryPC ℋ) (_root_.HaarUnitary.unitaryPC ℋ : Set _) = 1 := haarMeasure_self
      simpa [_root_.HaarUnitary.unitaryPC] using this⟩

end CompactHaar

/-! ## Section 2: Measurability and integrability of conjugation -/

section Measurability

variable {ℋ : Type u} [Qudit ℋ]

/-- Conjugation u ↦ (↑u) * X * (star ↑u) is continuous on the unitary group. -/
lemma continuous_unitaryConj (X : L ℋ) :
    Continuous (fun u : unitary (L ℋ) => (u : L ℋ) * X * (star (u : L ℋ))) := by
  have hval : Continuous (fun u : unitary (L ℋ) => (u : L ℋ)) := continuous_subtype_val
  have hstar : Continuous (fun u : unitary (L ℋ) => star (u : L ℋ)) :=
    continuous_star.comp hval
  exact ((hval.mul continuous_const).mul hstar)

/-- Conjugation is integrable with respect to `haarUnitary`. -/
lemma integrable_unitaryConj [Nontrivial ℋ] (X : L ℋ) :
    Integrable (fun u : unitary (L ℋ) => (u : L ℋ) * X * (star (u : L ℋ)))
      (haarUnitary ℋ) :=
  (continuous_unitaryConj X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

end Measurability

/-! ## Section 3: Twirl (Schur averaging) identity

The core result is `twirl_eq_smul_one`: averaging unitary conjugation over the
Haar measure produces a scalar multiple of the identity. This follows from two facts:
1. The averaged operator commutes with all unitaries (by Haar left-invariance).
2. An element of `L ℋ` commuting with all elements is a scalar (`IsCentral ℂ (L ℋ)`).
3. To bridge (1) → (2), one shows that unitaries ℂ-linearly span `L ℋ`.
The scalar is then determined by the trace.

The Schur orthogonality relation and the tensor-product twirl identity are
consequences of `twirl_eq_smul_one`.
-/

section Twirl

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The rank-one projection P_v = |v⟩⟨v| as a linear map. -/
 noncomputable def proj (v : ℋ) : L ℋ :=
  (InnerProductSpace.rankOne ℂ v v : ℋ →L[ℂ] ℋ).toLinearMap

omit [Nontrivial ℋ] in
 lemma proj_apply (v w : ℋ) : _root_.HaarUnitary.proj v w = @inner ℂ ℋ _ v w • v := by
  simp [_root_.HaarUnitary.proj, InnerProductSpace.rankOne_apply]

/-- The reflection R_v = 1 - 2|v⟩⟨v| as a linear map. -/
 noncomputable def refl' (v : ℋ) : L ℋ :=
  (1 : L ℋ) - (2 : ℂ) • _root_.HaarUnitary.proj v

omit [Nontrivial ℋ] in
 lemma refl'_apply (v w : ℋ) :
    _root_.HaarUnitary.refl' v w = w - (2 : ℂ) • @inner ℂ ℋ _ v w • v := by
  simp [_root_.HaarUnitary.refl', _root_.HaarUnitary.proj_apply, smul_smul]

omit [Nontrivial ℋ] in
 lemma star_proj (v : ℋ) : star (_root_.HaarUnitary.proj v) = _root_.HaarUnitary.proj v := by
  apply (_root_.HaarUnitary.iso ℋ).injective
  simp only [_root_.HaarUnitary.iso_star, _root_.HaarUnitary.proj]
  change star (InnerProductSpace.rankOne ℂ v v) = InnerProductSpace.rankOne ℂ v v
  rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

omit [Nontrivial ℋ] in
 lemma refl'_sq (v : ℋ) (hv : ‖v‖ = 1) : _root_.HaarUnitary.refl' v * _root_.HaarUnitary.refl' v = 1 := by
  have hiv : @inner ℂ ℋ _ v v = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hv]; simp
  ext w
  change _root_.HaarUnitary.refl' v (_root_.HaarUnitary.refl' v w) = w
  have h1 : _root_.HaarUnitary.refl' v w = w - (2 * @inner ℂ ℋ _ v w) • v := by
    rw [_root_.HaarUnitary.refl'_apply, smul_smul]
  have h2 : @inner ℂ ℋ _ v (_root_.HaarUnitary.refl' v w) = -@inner ℂ ℋ _ v w := by
    rw [h1, inner_sub_right, inner_smul_right, hiv]; ring
  rw [_root_.HaarUnitary.refl'_apply, h2, smul_smul, h1]
  simp only [mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

omit [Nontrivial ℋ] in
 lemma refl'_star (v : ℋ) : star (_root_.HaarUnitary.refl' v) = _root_.HaarUnitary.refl' v := by
  simp [_root_.HaarUnitary.refl', star_sub, star_one, star_smul, _root_.HaarUnitary.star_proj]

omit [Nontrivial ℋ] in
 lemma refl'_unitary (v : ℋ) (hv : ‖v‖ = 1) : _root_.HaarUnitary.refl' v ∈ unitary (L ℋ) := by
  rw [Unitary.mem_iff]
  exact ⟨by rw [_root_.HaarUnitary.refl'_star, _root_.HaarUnitary.refl'_sq v hv], by rw [_root_.HaarUnitary.refl'_star, _root_.HaarUnitary.refl'_sq v hv]⟩

/-- An element of `L ℋ` that commutes with all unitaries is a scalar multiple
    of the identity. Uses reflection unitaries and the eigenvector argument. -/
lemma scalar_of_commutes_unitaries (M : L ℋ)
    (hM : ∀ V : unitary (L ℋ), (V : L ℋ) * M = M * (V : L ℋ)) :
    ∃ c : ℂ, M = c • (1 : L ℋ) := by
  -- Step 1: for unit v and any x, ⟨v, Mx⟩ v = ⟨v, x⟩ Mv (from reflection commutation)
  have proj_comm : ∀ (v : ℋ), ‖v‖ = 1 → ∀ (x : ℋ),
      @inner ℂ ℋ _ v (M x) • v = @inner ℂ ℋ _ v x • M v := by
    intro v hv x
    have h : _root_.HaarUnitary.refl' v (M x) = M (_root_.HaarUnitary.refl' v x) :=
      congr_fun (congr_arg DFunLike.coe (hM ⟨_root_.HaarUnitary.refl' v, _root_.HaarUnitary.refl'_unitary v hv⟩)) x
    rw [_root_.HaarUnitary.refl'_apply, _root_.HaarUnitary.refl'_apply, map_sub, map_smul, map_smul, smul_smul, smul_smul] at h
    have h' := congr_arg Neg.neg h
    simp only [neg_sub] at h'
    have hsub := sub_left_injective h'
    rw [mul_smul, mul_smul] at hsub
    exact smul_right_injective ℋ (two_ne_zero (α := ℂ)) hsub
  -- Step 2: for unit v, M v = ⟨v, Mv⟩ v
  have unit_eig : ∀ (v : ℋ), ‖v‖ = 1 → M v = @inner ℂ ℋ _ v (M v) • v := by
    intro v hv
    have h := proj_comm v hv v
    rw [show @inner ℂ ℋ _ v v = (1 : ℂ) from by
      rw [inner_self_eq_norm_sq_to_K, hv]; simp, one_smul] at h
    exact h.symm
  -- Step 3: the eigenvalue is constant across all unit vectors
  have eig_const : ∀ (v w : ℋ), ‖v‖ = 1 → ‖w‖ = 1 →
      @inner ℂ ℋ _ v (M v) = @inner ℂ ℋ _ w (M w) := by
    intro v w hv hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact one_ne_zero hw.symm
    by_cases hvw : v + w = 0
    · have hwv : w = -v := eq_neg_of_add_eq_zero_right hvw
      rw [hwv, map_neg, inner_neg_left, inner_neg_right, neg_neg]
    · by_cases hli : LinearIndependent ℂ ![v, w]
      · have hvwn : ‖v + w‖ ≠ 0 := norm_ne_zero_iff.mpr hvw
        set u := ((↑‖v + w‖ : ℂ)⁻¹) • (v + w) with hu_def
        have hcinv : ((↑‖v + w‖ : ℂ)⁻¹) ≠ 0 :=
          inv_ne_zero (Complex.ofReal_ne_zero.mpr hvwn)
        have hu : ‖u‖ = 1 := by
          rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
              inv_mul_cancel₀ hvwn]
        set lv := @inner ℂ ℋ _ v (M v)
        set lw := @inner ℂ ℋ _ w (M w)
        have hMu2 : M u = (↑‖v + w‖ : ℂ)⁻¹ • (lv • v + lw • w) := by
          conv_lhs => rw [hu_def, map_smul, map_add, unit_eig v hv, unit_eig w hw]
        have hMu1 : M u = @inner ℂ ℋ _ u (M u) • u := unit_eig u hu
        have h3 := hMu1.symm.trans hMu2
        rw [hu_def, smul_comm] at h3
        have key : @inner ℂ ℋ _ u (M u) • (v + w) = lv • v + lw • w :=
          smul_right_injective ℋ hcinv h3
        rw [smul_add] at key
        have hsub : (@inner ℂ ℋ _ u (M u) - lv) • v +
            (@inner ℂ ℋ _ u (M u) - lw) • w = 0 := by
          rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]; exact key
        obtain ⟨h1, h2⟩ := hli.eq_zero_of_pair hsub
        exact (sub_eq_zero.mp h1).symm.trans (sub_eq_zero.mp h2)
      · simp only [linearIndependent_fin2, Matrix.cons_val_one,
            Matrix.cons_val_zero, not_and_or, not_forall, Classical.not_not] at hli
        rcases hli with hw0' | ⟨a, ha⟩
        · exact absurd hw0' hw0
        · set lv := @inner ℂ ℋ _ v (M v)
          set lw := @inner ℂ ℋ _ w (M w)
          have ha0 : a ≠ 0 := by
            intro h; rw [h, zero_smul] at ha
            have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; exact one_ne_zero hv.symm
            exact hv0 ha.symm
          have h2 : M v = (a * lw) • w := by
            conv_lhs => rw [← ha, map_smul, unit_eig w hw]; rw [smul_smul]
          have h3 : lv • v = (a * lw) • w := (unit_eig v hv).symm.trans h2
          rw [show v = a • w from ha.symm, smul_smul] at h3
          have h4 : (lv * a - a * lw) • w = 0 := by rw [sub_smul, sub_eq_zero]; exact h3
          have h5 : lv * a = a * lw := sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw0)
          exact mul_left_cancel₀ ha0 (by rwa [mul_comm lv a] at h5)
  -- Step 4: define c and show M = c • 1
  obtain ⟨e, he⟩ : ∃ e : ℋ, ‖e‖ = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ℋ)
    exact ⟨(‖v‖⁻¹ : ℝ) • v, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  refine ⟨@inner ℂ ℋ _ e (M e), ?_⟩
  ext x
  change M x = @inner ℂ ℋ _ e (M e) • ((1 : L ℋ) x)
  rw [show (1 : L ℋ) x = x from rfl]
  by_cases hx : x = 0
  · simp [hx]
  · set u := ((↑‖x‖ : ℂ)⁻¹) • x with hu_def
    have hcinv : ((↑‖x‖ : ℂ)⁻¹) ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hMu := unit_eig u hu
    rw [eig_const u e hu he] at hMu
    rw [hu_def, map_smul, smul_comm] at hMu
    exact smul_right_injective ℋ hcinv hMu

theorem twirl_eq_smul_one (X : L ℋ) :
    ∫ u : unitary (L ℋ), (u : L ℋ) * X * star (u : L ℋ) ∂(haarUnitary ℋ) =
    ((Module.finrank ℂ ℋ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ X) • (1 : L ℋ) := by
  set Φ := ∫ u : unitary (L ℋ), (u : L ℋ) * X * star (u : L ℋ) ∂(haarUnitary ℋ)
  -- Step 1: Φ commutes with all unitaries V (by Haar left-invariance)
  have hΦ_comm : ∀ V : unitary (L ℋ), (V : L ℋ) * Φ = Φ * (V : L ℋ) := by
    intro V
    suffices h_conj : (V : L ℋ) * Φ * star (V : L ℋ) = Φ by
      have hVV : star (↑V : L ℋ) * ↑V = 1 := (Unitary.mem_iff.mp V.property).1
      calc (↑V : L ℋ) * Φ
          = ↑V * Φ * 1 := (mul_one _).symm
        _ = ↑V * Φ * (star ↑V * ↑V) := by rw [hVV]
        _ = ↑V * Φ * star ↑V * ↑V := by rw [mul_assoc (↑V * Φ)]
        _ = Φ * ↑V := by rw [h_conj]
    let conjV : L ℋ →L[ℂ] L ℋ := ⟨{
      toFun := fun A => (V : L ℋ) * A * star (V : L ℋ)
      map_add' := fun A B => by rw [mul_add, add_mul]
      map_smul' := fun c A => by rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
    }, (continuous_const.mul continuous_id).mul continuous_const⟩
    have h_pull := conjV.integral_comp_comm (integrable_unitaryConj X)
    have hfVu : ∀ u : unitary (L ℋ),
        conjV ((u : L ℋ) * X * star (u : L ℋ)) =
        ((V * u : unitary (L ℋ)) : L ℋ) * X * star ((V * u : unitary (L ℋ)) : L ℋ) := by
      intro u
      change (V : L ℋ) * ((u : L ℋ) * X * star (u : L ℋ)) * star (V : L ℋ) = _
      simp only [MulMemClass.coe_mul, star_mul, mul_assoc]
    simp_rw [hfVu] at h_pull
    have h_haar := integral_mul_left_eq_self (μ := haarUnitary ℋ)
      (fun u : unitary (L ℋ) => (u : L ℋ) * X * star (u : L ℋ)) V
    exact (h_pull.symm.trans h_haar)
  -- Step 2: Φ is scalar (from scalar_of_commutes_unitaries)
  obtain ⟨c, hc⟩ := scalar_of_commutes_unitaries Φ hΦ_comm
  -- Step 3: determine c from trace (Tr(Φ) = Tr(X) since trace is cyclic and Haar is prob.)
  have hc_val : c = (Module.finrank ℂ ℋ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ X := by
    have hd : (Module.finrank ℂ ℋ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ)).ne'
    have h1 : LinearMap.trace ℂ ℋ Φ = c * (Module.finrank ℂ ℋ : ℂ) := by
      rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul]
    have h2 : LinearMap.trace ℂ ℋ Φ = LinearMap.trace ℂ ℋ X := by
      let trCLM : L ℋ →L[ℂ] ℂ := { LinearMap.trace ℂ ℋ with }
      have h_tr := trCLM.integral_comp_comm (integrable_unitaryConj X)
      have h_cycl : ∀ u : unitary (L ℋ),
          trCLM ((u : L ℋ) * X * star (u : L ℋ)) = LinearMap.trace ℂ ℋ X := by
        intro u
        change LinearMap.trace ℂ ℋ ((u : L ℋ) * X * star (u : L ℋ)) = _
        rw [LinearMap.trace_mul_cycle,
            show star (↑u : L ℋ) * (↑u : L ℋ) = 1 from (Unitary.mem_iff.mp u.property).1,
            one_mul]
      simp_rw [h_cycl] at h_tr
      simp only [integral_const, probReal_univ, one_smul] at h_tr
      exact h_tr.symm
    have h := h1.symm.trans h2
    rw [← h, mul_comm c (Module.finrank ℂ ℋ : ℂ), ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [hc, hc_val]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]



variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]







-- Forward direction on rank-one operators (dualTensorHom ⊗ dualTensorHom):
-- trace through the chain of 8 linear equivalences in l_tensor_equiv.
omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma l_tensor_forward_rankone (f₁ : Module.Dual ℂ ℋ₁) (u₁ : ℋ₁)
    (f₂ : Module.Dual ℂ ℋ₂) (u₂ : ℋ₂) :
    l_tensor_equiv (dualTensorHomEquiv ℂ (ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₁ ⊗[ℂ] ℋ₂)
      (TensorProduct.dualDistribEquiv ℂ ℋ₁ ℋ₂ (f₁ ⊗ₜ[ℂ] f₂) ⊗ₜ[ℂ] (u₁ ⊗ₜ[ℂ] u₂))) =
    dualTensorHomEquiv ℂ ℋ₁ ℋ₁ (f₁ ⊗ₜ[ℂ] u₁) ⊗ₜ[ℂ] dualTensorHomEquiv ℂ ℋ₂ ℋ₂ (f₂ ⊗ₜ[ℂ] u₂) := by
  unfold l_tensor_equiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.rTensor_tmul, LinearEquiv.lTensor_tmul,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul,
    TensorProduct.comm_tmul, TensorProduct.congr_tmul]

-- Extend to all operators by surjectivity of dualTensorHomEquiv and bilinearity.
omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma l_tensor_equiv_forward_tmul (A : L ℋ₁) (B : L ℋ₂) :
    l_tensor_equiv (TensorProduct.map A B) = A ⊗ₜ[ℂ] B := by
  obtain ⟨a, rfl⟩ := (dualTensorHomEquiv ℂ ℋ₁ ℋ₁).surjective A
  obtain ⟨b, rfl⟩ := (dualTensorHomEquiv ℂ ℋ₂ ℋ₂).surjective B
  induction a using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, TensorProduct.map_zero_left, map_zero, TensorProduct.zero_tmul]
  | add a₁ a₂ ha₁ ha₂ =>
    simp only [map_add, TensorProduct.map_add_left, map_add, TensorProduct.add_tmul]
    exact congr_arg₂ (· + ·) ha₁ ha₂
  | tmul f₁ u₁ =>
    induction b using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, TensorProduct.map_zero_right, map_zero, TensorProduct.tmul_zero]
    | add b₁ b₂ hb₁ hb₂ =>
      simp only [map_add, TensorProduct.map_add_right, map_add, TensorProduct.tmul_add]
      exact congr_arg₂ (· + ·) hb₁ hb₂
    | tmul f₂ u₂ =>
      change l_tensor_equiv
        (TensorProduct.map ((dualTensorHom ℂ ℋ₁ ℋ₁) (f₁ ⊗ₜ[ℂ] u₁))
          ((dualTensorHom ℂ ℋ₂ ℋ₂) (f₂ ⊗ₜ[ℂ] u₂))) =
        (dualTensorHom ℂ ℋ₁ ℋ₁) (f₁ ⊗ₜ[ℂ] u₁) ⊗ₜ[ℂ] (dualTensorHom ℂ ℋ₂ ℋ₂) (f₂ ⊗ₜ[ℂ] u₂)
      rw [map_dualTensorHom]
      exact _root_.HaarUnitary.l_tensor_forward_rankone f₁ u₁ f₂ u₂

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma l_tensor_equiv_symm_tmul (A : L ℋ₁) (B : L ℋ₂) :
    l_tensor_equiv.symm (A ⊗ₜ[ℂ] B) = TensorProduct.map A B := by
  apply l_tensor_equiv.injective
  rw [LinearEquiv.apply_symm_apply, _root_.HaarUnitary.l_tensor_equiv_forward_tmul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma Tr₂_map (A : L ℋ₁) (B : L ℋ₂) :
    QuantumChannel.Tr₂ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
    LinearMap.trace ℂ ℋ₁ A • B := by
  unfold QuantumChannel.Tr₂
  simp only [LinearMap.comp_apply]
  rw [show l_tensor_equiv.toLinearMap (TensorProduct.map A B) =
      l_tensor_equiv (TensorProduct.map A B) from rfl,
    ← _root_.HaarUnitary.l_tensor_equiv_symm_tmul (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A B,
    LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  change (TensorProduct.lid ℂ (L ℋ₂)) (LinearMap.trace ℂ ℋ₁ A ⊗ₜ[ℂ] B) =
    LinearMap.trace ℂ ℋ₁ A • B
  exact TensorProduct.lid_tmul B (LinearMap.trace ℂ ℋ₁ A)

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
 lemma map_add_right (f : L ℋ₁) (g₁ g₂ : L ℋ₂) :
    TensorProduct.map f (g₁ + g₂) =
    TensorProduct.map f g₁ + TensorProduct.map f g₂ := by
  simp only [map_eq_rTensor_mul_lTensor, map_add (lTensorStarAlgHom (ℋ₁ := ℋ₁)), mul_add]



/-! ### Right-factor twirl (mirror of `twirl_eq_partialTrace_smul_id`) -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- `conjugateEnd` by the tensor swap turns `T A B` into `T B A`. -/
 lemma conjugateEnd_comm_map (A : L ℋ₁) (B : L ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂))
        (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (TensorProduct.map B A : L (ℋ₂ ⊗[ℂ] ℋ₁)) := by
  apply TensorProduct.ext'
  intro y x
  change (TensorProduct.comm ℂ ℋ₁ ℋ₂).toLinearMap
        ((TensorProduct.map A B) ((TensorProduct.comm ℂ ℋ₁ ℋ₂).symm.toLinearMap (y ⊗ₜ[ℂ] x))) =
       (TensorProduct.map B A) (y ⊗ₜ[ℂ] x)
  simp [TensorProduct.map_tmul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Partial trace formula for `TrRight` applied to a tensor product:
    `TrRight (T A B) = (Tr B) • A`. -/
 lemma TrRight_map (A : L ℋ₁) (B : L ℋ₂) :
    QuantumChannel.TrRight (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
    LinearMap.trace ℂ ℋ₂ B • A := by
  -- TrRight = Tr₂ ∘ conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)
  unfold QuantumChannel.TrRight
  simp only [LinearMap.comp_apply]
  rw [_root_.HaarUnitary.conjugateEnd_comm_map A B]
  exact _root_.HaarUnitary.Tr₂_map B A

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Right-additivity for `TensorProduct.map` in the second argument (already exists
    as `map_add_right`). This is the analog for the first argument. -/
 lemma map_add_left (f₁ f₂ : L ℋ₁) (g : L ℋ₂) :
    TensorProduct.map (f₁ + f₂) g =
    TensorProduct.map f₁ g + TensorProduct.map f₂ g := by
  simp only [map_eq_rTensor_mul_lTensor, map_add (rTensorStarAlgHom (ℋ₂ := ℋ₂)), add_mul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensor-product conjugation on the right factor is continuous. -/
lemma continuous_unitaryConj_tensor_right (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (L ℋ₂) =>
      TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) * X *
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star (u : L ℋ₂))) := by
  have h_id_eq : ∀ g : L ℋ₂,
      TensorProduct.map (LinearMap.id (M := ℋ₁)) g = (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
    intro g
    rw [show (LinearMap.id : L ℋ₁) = 1 from rfl,
        map_eq_rTensor_mul_lTensor, map_one (rTensorStarAlgHom (ℋ₂ := ℋ₂)), one_mul]
  simp_rw [h_id_eq]
  exact (((continuous_lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
    continuous_subtype_val).mul continuous_const).mul
    ((continuous_lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
      (continuous_star.comp continuous_subtype_val))

omit [Nontrivial ℋ₁] in
/-- Tensor-product conjugation on the right factor is integrable. -/
lemma integrable_unitaryConj_tensor_right (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (L ℋ₂) =>
      TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) * X *
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star (u : L ℋ₂)))
      (haarUnitary ℋ₂) :=
  (continuous_unitaryConj_tensor_right X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

omit [Nontrivial ℋ₁] in
/-- **Right-factor twirl identity** (mirror of `twirl_eq_partialTrace_smul_id`).

    ∫ (1⊗u) X (1⊗u*) du = TrRight(X) ⊗ dim(ℋ₂)⁻¹ • id_{ℋ₂}

    where the integral is over normalized Haar measure on `unitary (L ℋ₂)`. -/
theorem twirl_eq_partialTrace_right_smul_id (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (L ℋ₂),
      TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) * X *
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star (u : L ℋ₂))
    ∂(haarUnitary ℋ₂) =
    TensorProduct.map (QuantumChannel.TrRight X)
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • LinearMap.id (M := ℋ₂)) := by
  suffices h : ∀ Y : L ℋ₁ ⊗[ℂ] L ℋ₂,
      ∫ u : unitary (L ℋ₂),
        TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) *
        l_tensor_equiv.symm Y *
        TensorProduct.map (LinearMap.id (M := ℋ₁)) (star (u : L ℋ₂))
      ∂(haarUnitary ℋ₂) =
      TensorProduct.map
        (QuantumChannel.TrRight (l_tensor_equiv.symm Y))
        ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • LinearMap.id (M := ℋ₂)) by
    have := h (l_tensor_equiv X)
    simp only [LinearEquiv.symm_apply_apply] at this
    exact this
  intro Y
  induction Y using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, mul_zero, zero_mul, integral_zero]
    symm; exact TensorProduct.ext' fun v₁ v₂ => by simp
  | tmul A B =>
    rw [_root_.HaarUnitary.l_tensor_equiv_symm_tmul, _root_.HaarUnitary.TrRight_map]
    have h_simp : ∀ u : unitary (L ℋ₂),
        TensorProduct.map (LinearMap.id (M := ℋ₁)) ((u : L ℋ₂)) *
        TensorProduct.map A B *
        TensorProduct.map (LinearMap.id (M := ℋ₁)) (star (u : L ℋ₂)) =
        TensorProduct.map A ((u : L ℋ₂) * B * star (u : L ℋ₂)) := fun u =>
      TensorProduct.ext' fun v₁ v₂ => by simp [TensorProduct.map_tmul]
    simp_rw [h_simp]
    -- Goal: ∫ map A (u*B*star u) du = map (Tr B • A) (dim⁻¹ • id)
    let mapA_lm : L ℋ₂ →ₗ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) :=
      { toFun := fun g => TensorProduct.map A g
        map_add' := fun g h => _root_.HaarUnitary.map_add_right A g h
        map_smul' := fun c g => by
          simp only [RingHom.id_apply, map_eq_rTensor_mul_lTensor,
            map_smul (lTensorStarAlgHom (ℋ₁ := ℋ₁)), mul_smul_comm] }
    let mapA : L ℋ₂ →L[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) := ⟨mapA_lm, map_continuous mapA_lm⟩
    calc ∫ u : unitary (L ℋ₂),
            TensorProduct.map A ((u : L ℋ₂) * B * star (u : L ℋ₂))
            ∂(haarUnitary ℋ₂)
        = mapA (∫ u : unitary (L ℋ₂),
            (u : L ℋ₂) * B * star (u : L ℋ₂) ∂(haarUnitary ℋ₂)) :=
          mapA.integral_comp_comm (integrable_unitaryConj B)
      _ = TensorProduct.map
            (LinearMap.trace ℂ ℋ₂ B • A)
            ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • LinearMap.id (M := ℋ₂)) := by
          rw [twirl_eq_smul_one B]
          change TensorProduct.map A
            (((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₂ B) • (1 : L ℋ₂)) =
            TensorProduct.map (LinearMap.trace ℂ ℋ₂ B • A)
              ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂))
          rw [map_eq_rTensor_mul_lTensor
                A (((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₂ B) • (1 : L ℋ₂)),
              map_eq_rTensor_mul_lTensor
                (LinearMap.trace ℂ ℋ₂ B • A)
                ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂))]
          simp only [map_smul, map_one, mul_smul_comm, mul_one, smul_smul]
  | add Y₁ Y₂ hY₁ hY₂ =>
    rw [show (l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (Y₁ + Y₂) =
        l_tensor_equiv.symm Y₁ + l_tensor_equiv.symm Y₂ from map_add _ _ _]
    simp only [mul_add, add_mul]
    rw [integral_add
      (integrable_unitaryConj_tensor_right (l_tensor_equiv.symm Y₁))
      (integrable_unitaryConj_tensor_right (l_tensor_equiv.symm Y₂)),
      show QuantumChannel.TrRight (l_tensor_equiv.symm Y₁ + l_tensor_equiv.symm Y₂) =
        QuantumChannel.TrRight (l_tensor_equiv.symm Y₁) +
        QuantumChannel.TrRight (l_tensor_equiv.symm Y₂) from map_add _ _ _,
      _root_.HaarUnitary.map_add_left]
    exact congr_arg₂ (· + ·) hY₁ hY₂

end Twirl

/-! ## Section 4: Jensen inequality for jointly convex/concave operator functions -/

section Jensen

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
/-- **Jensen's inequality for jointly convex functions under probability measure**.
    If f : L ℋ → L ℋ → ℝ is jointly convex on S × T, continuous on S × T, and
    g₁(u) ∈ S, g₂(u) ∈ T for μ-a.e. u (where μ is a probability measure), then
    f(∫ g₁ dμ, ∫ g₂ dμ) ≤ ∫ f(g₁(u), g₂(u)) dμ. -/
theorem jointly_convex_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (L ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : L ℋ → L ℋ → ℝ}
    (hf_conv : JointlyConvexOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → L ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ)
    (_hmem₁ : ∫ x, g₁ x ∂μ ∈ S) (_hmem₂ : ∫ x, g₂ x ∂μ ∈ T) :
    f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) ≤ ∫ x, f (g₁ x) (g₂ x) ∂μ := by
  have hF : ConvexOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change f (c • a₁ + d • a₂) (c • b₁ + d • b₂) ≤ c • f a₁ b₁ + d • f a₂ b₂
      have : c = 1 - d := by linarith
      rw [this]; exact hf_conv ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.map_integral_le hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

omit [Nontrivial ℋ] in
/-- **Jensen's inequality for jointly concave functions under probability measure**.
    If f : L ℋ → L ℋ → ℝ is jointly concave on S × T, then
    ∫ f(g₁(u), g₂(u)) dμ ≤ f(∫ g₁ dμ, ∫ g₂ dμ). -/
theorem jointly_concave_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (L ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : L ℋ → L ℋ → ℝ}
    (hf_conc : JointlyConcaveOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → L ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ)
    (_hmem₁ : ∫ x, g₁ x ∂μ ∈ S) (_hmem₂ : ∫ x, g₂ x ∂μ ∈ T) :
    (∫ x, f (g₁ x) (g₂ x) ∂μ) ≤ f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) := by
  have hF : ConcaveOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change c • f a₁ b₁ + d • f a₂ b₂ ≤ f (c • a₁ + d • a₂) (c • b₁ + d • b₂)
      have : c = 1 - d := by linarith
      rw [this]; exact hf_conc ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.le_map_integral hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

end Jensen

/-! ## Section 5: Stinespring–Haar identity (Equation (1) of Frank–Lieb) -/

section StinespringHaar

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁]



end StinespringHaar

end HaarUnitary


