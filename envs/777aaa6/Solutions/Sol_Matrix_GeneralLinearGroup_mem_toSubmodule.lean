-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.mem_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:49:55.194413+00:00
-- url     : https://prove2.me/submissions/f6ce7564-cbd2-4ea7-8e42-738f423ddd25

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
open Matrix.GeneralLinearGroup
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}
namespace Matrix.GeneralLinearGroup
theorem _root_.solution (g : GL ι K) (x : ι → K) :
    x ∈ g.toSubmodule (R := R) ↔ ∃ (y : ι → R), g *ᵥ (Subtype.val ∘ y) = x := by
  simp only [toSubmodule, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      use Pi.single i 1
      ext
      simp
    | zero =>
      use 0
      simp only [Pi.comp_zero, ZeroMemClass.coe_zero, Function.const_zero, mulVec_zero]
    | add v w _ _ hv hw =>
      obtain ⟨v, hv⟩ := hv
      obtain ⟨w, hw⟩ := hw
      use v + w
      simp only [Subtype.val_comp_add]
      rw [mulVec_add, hw, hv]
    | smul a x _ hv =>
      obtain ⟨v, hv⟩ := hv
      use a • v
      simp only [Subtype.val_comp_smul]
      change g.val *ᵥ ((a : K) • (Subtype.val ∘ v)) = (a : K) • x
      rw [mulVec_smul, hv]
  · rintro ⟨v, rfl⟩
    let b := Pi.basisFun R ι
    have hv : v ∈ Submodule.span R (Set.range b) := Basis.mem_span b v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      apply Submodule.subset_span
      use i
      simp only [b]
      simp only [Pi.basisFun_apply, mulVec_single_one, b, Pi.single]
      show _ = g.val *ᵥ (Subtype.val ∘ Pi.single i 1)
      ext
      simp
    | zero =>
      simp only [Pi.comp_zero, ZeroMemClass.coe_zero, Function.const_zero, mulVec_zero,
        Submodule.zero_mem]
    | add _ _ _ _ hv hw =>
      rw [Subtype.val_comp_add, mulVec_add]
      exact Submodule.add_mem _ hv hw
    | smul a v _ hv =>
      rw [Subtype.val_comp_smul]
      change g.val *ᵥ ((a : K) • (Subtype.val ∘ v)) ∈ _
      rw [mulVec_smul]
      exact Submodule.smul_mem _ a hv
end Matrix.GeneralLinearGroup
