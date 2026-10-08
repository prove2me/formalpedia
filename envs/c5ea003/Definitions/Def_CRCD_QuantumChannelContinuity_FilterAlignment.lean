-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
-- name    : CRCD_QuantumChannelContinuity_FilterAlignment
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:00:09.661986+00:00
-- url     : https://prove2.me/theorems/39b2cf0d-e91a-4ff0-b943-906018499e19
-- title:
--   Environmental coefficients of a supplied dilation
-- statement:
--   For $b\in B$, the output slice of $v\in B\otimes E$ is $(\langle b,\cdot\rangle\otimes I_E)v$. Given orthonormal bases $(a_i)$ of $A$ and $(b_j)$ of $B$, the environmental coefficient map of a dilation $V:A\to B\otimes E$ sends $a_i\otimes b_j$ to the output slice of $V(a_i)$ against $b_j$. This reshuffles the supplied dilation without replacing its environment. The associated Gram identities and basis expansions support alignment of dilations under completely positive order, so that the resulting contraction acts on the original environmental degrees of freedom.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/FilterAlignment.lean#L27-L249

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Alignment of supplied dilations

The environmental coefficient Gram matrix is recovered from the channel on
rank-one input operators.  Douglas factorization then aligns two supplied
dilations by a contraction, including nonminimal and singular dilations.
-/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder BigOperators

namespace QuantumChannelContinuity

universe u
variable {A B E F : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit F]

set_option maxHeartbeats 800000

/-- Extract an environmental coefficient against an output vector. -/
noncomputable def outputSlice (b : B) : B ⊗[ℂ] E →ₗ[ℂ] E :=
  (TensorProduct.lid ℂ E).toLinearMap.comp
    (TensorProduct.map (InnerProductSpace.toDualMap ℂ B b) LinearMap.id)

@[simp] theorem outputSlice_tmul (b x : B) (y : E) :
    outputSlice b (x ⊗ₜ[ℂ] y) = inner ℂ b x • y := by
  simp [outputSlice]

theorem trRight_outer_product_tmul (b c : B) (e f : E) :
    TrRight (outer_product (b ⊗ₜ[ℂ] e) (c ⊗ₜ[ℂ] f)) =
      inner ℂ e f • outer_product b c := by
  rw [← l_tensor_equiv_symm_outer_product, l_tensor_equiv_symm_tmul,
    trRight_map, trace_outer_product]

 theorem outer_product_add_left' (u v w : B ⊗[ℂ] E) :
    outer_product (u + v) w = outer_product u w + outer_product v w := by
  ext x
  simp [outer_product_eq_rankOne]

 theorem outer_product_add_right' (u v w : B ⊗[ℂ] E) :
    outer_product u (v + w) = outer_product u v + outer_product u w := by
  ext x
  simp [outer_product_eq_rankOne]

/-- Partial trace recovers the Gram products of environmental coefficients. -/
theorem inner_outputSlice (b c : B) (x y : B ⊗[ℂ] E) :
    inner ℂ (outputSlice b x) (outputSlice c y) =
      inner ℂ c ((TrRight (outer_product x y)) b) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [outer_product_eq_rankOne]
  | tmul d e =>
    induction y using TensorProduct.induction_on with
    | zero => simp [outer_product_eq_rankOne]
    | tmul f g =>
      rw [trRight_outer_product_tmul]
      simp only [outputSlice_tmul, inner_smul_left, inner_smul_right,
        LinearMap.smul_apply, outer_product_eq_rankOne,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      simp only [inner_conj_symm]
      ring
    | add y z hy hz =>
      simp only [map_add, inner_add_right, _root_.QuantumChannelContinuity.outer_product_add_right',
        LinearMap.add_apply, hy, hz]
  | add x z hx hz =>
    simp only [map_add, inner_add_left, _root_.QuantumChannelContinuity.outer_product_add_left',
      LinearMap.add_apply, inner_add_right, hx, hz]

theorem outputSlice_environmentMap (U : E →ₗ[ℂ] F) (b : B) (x : B ⊗[ℂ] E) :
    outputSlice b (environmentMap U x) = U (outputSlice b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d e => simp [environmentMap]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem outputSlice_expand {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ B) (x : B ⊗[ℂ] E) :
    x = ∑ i, b i ⊗ₜ[ℂ] outputSlice (b i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d e =>
    calc
      d ⊗ₜ[ℂ] e = (∑ i, b.repr d i • b i) ⊗ₜ[ℂ] e := by rw [b.sum_repr]
      _ = _ := by
        simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul', outputSlice_tmul,
          TensorProduct.tmul_smul, b.repr_apply_apply]
  | add x y hx hy =>
    simpa only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) hx hy

theorem outputSlice_ext {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ B) {x y : B ⊗[ℂ] E}
    (h : ∀ i, outputSlice (b i) x = outputSlice (b i) y) : x = y := by
  rw [outputSlice_expand b x, outputSlice_expand b y]
  simp only [h]

theorem dilationChannel_outer_product (V : A →ₗ[ℂ] B ⊗[ℂ] E) (a c : A) :
    dilationChannel V (outer_product a c) = TrRight (outer_product (V a) (V c)) := by
  simp only [dilationChannel, LinearMap.comp_apply, krausTerm,
    LinearMap.coe_mk, AddHom.coe_mk, comp_outer_product_adjoint]



/-- Reshuffle a supplied dilation into its environmental coefficient map. -/
noncomputable def dilationCoefficients {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) : A ⊗[ℂ] B →ₗ[ℂ] E :=
  (a.tensorProduct b).toBasis.constr ℂ (fun p => outputSlice (b p.2) (V (a p.1)))

@[simp] theorem dilationCoefficients_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (i : ι) (j : κ) :
    dilationCoefficients a b V (a i ⊗ₜ[ℂ] b j) = outputSlice (b j) (V (a i)) := by
  simpa only [dilationCoefficients, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.tensorProduct_apply] using
    (a.tensorProduct b).toBasis.constr_basis ℂ
      (fun p => outputSlice (b p.2) (V (a p.1))) (i, j)







theorem dilation_coefficient_gram_add {G : Type u} [Qudit G]
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (R : A →ₗ[ℂ] B ⊗[ℂ] G)
    (hV : dilationChannel V = dilationChannel W + dilationChannel R)
    (a c : A) (b d : B) :
    inner ℂ (outputSlice b (V a)) (outputSlice d (V c)) =
      inner ℂ (outputSlice b (W a)) (outputSlice d (W c)) +
      inner ℂ (outputSlice b (R a)) (outputSlice d (R c)) := by
  rw [inner_outputSlice, inner_outputSlice, inner_outputSlice]
  have h := congrArg (fun Φ : QuantumChannel.T A B => Φ (outer_product a c)) hV
  change dilationChannel V (outer_product a c) =
    dilationChannel W (outer_product a c) + dilationChannel R (outer_product a c) at h
  simp only [dilationChannel_outer_product] at h
  rw [h, LinearMap.add_apply, inner_add_right]

theorem dilationCoefficients_inner_add {ι κ : Type*} {G : Type u}
    [Fintype ι] [Fintype κ] [Qudit G]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (R : A →ₗ[ℂ] B ⊗[ℂ] G)
    (hV : dilationChannel V = dilationChannel W + dilationChannel R)
    (x y : A ⊗[ℂ] B) :
    inner ℂ (dilationCoefficients a b V x) (dilationCoefficients a b V y) =
      inner ℂ (dilationCoefficients a b W x) (dilationCoefficients a b W y) +
      inner ℂ (dilationCoefficients a b R x) (dilationCoefficients a b R y) := by
  simp only [dilationCoefficients, Module.Basis.constr_apply_fintype,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    dilation_coefficient_gram_add V W R hV, mul_add, Finset.sum_add_distrib]

/-- Complete-positive order gives an environmental contraction between any
two supplied dilations.  This is the finite-dimensional CP Radon–Nikodym
factorization in the form used by the filter construction. -/
theorem exists_ordered_dilation_factor
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (hVW : CPLe (dilationChannel V) (dilationChannel W)) :
    ∃ U : F →ₗ[ℂ] E, (LinearMap.adjoint U).comp U ≤ 1 ∧
      (environmentMap (B := B) U).comp W = V := by
  let a := stdOrthonormalBasis ℂ A
  let b := stdOrthonormalBasis ℂ B
  obtain ⟨G, instG, hrep⟩ := cp_to_stinespring a.toBasis
    (dilationChannel W - dilationChannel V) hVW
  letI := instG
  obtain ⟨R, hR⟩ := hrep
  have hR' : dilationChannel R = dilationChannel W - dilationChannel V := by
    ext1 X
    exact (hR X).symm
  have hsum : dilationChannel W = dilationChannel V + dilationChannel R := by
    rw [hR']
    abel
  obtain ⟨U, hU, hfactor⟩ := exists_contraction_factor
    (dilationCoefficients a b V) (dilationCoefficients a b W) (by
      intro x
      have h := congrArg RCLike.re
        (dilationCoefficients_inner_add a b W V R hsum x x)
      simp only [map_add, inner_self_eq_norm_sq (𝕜 := ℂ)] at h
      nlinarith [sq_nonneg ‖dilationCoefficients a b R x‖,
        norm_nonneg (dilationCoefficients a b V x),
        norm_nonneg (dilationCoefficients a b W x)])
  refine ⟨U, hU, ?_⟩
  apply a.toBasis.ext
  intro i
  apply outputSlice_ext b
  intro j
  have h := congrArg (fun L : A ⊗[ℂ] B →ₗ[ℂ] E => L (a i ⊗ₜ[ℂ] b j)) hfactor
  simp only [LinearMap.comp_apply, dilationCoefficients_basis] at h
  simpa only [LinearMap.comp_apply, outputSlice_environmentMap] using h.symm

end QuantumChannelContinuity


