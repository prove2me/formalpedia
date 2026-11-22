-- Prove2me | solution 1 for Basis.smulGL_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:21:51.776278+00:00
-- url     : https://prove2.me/submissions/ec601eeb-e3bf-4a6c-b1c0-4411fc9a031c

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_smulGL_def
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_smul
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] Basis.restrict_apply
attribute [local simp] Basis.restrictToLattice_apply
attribute [local simp] Basis.smulGL_apply

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [DecidableEq ι] [Fintype ι]
namespace Basis
theorem _root_.solution (g : GL ι K) (b : Basis ι K (ι → K)) :
    (g • b).toSubmodule (R := R) = g • b.toSubmodule := by
  classical
  simp only [toSubmodule, smulGL_def]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro - ⟨i, hi, rfl⟩
    simp only [map_apply, Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply, SetLike.mem_coe]
    rw [Matrix.GeneralLinearGroup.mem_smul]
    refine ⟨b i, ?_, rfl⟩
    apply Submodule.subset_span
    exact Set.mem_range_self i
  · intro x hx
    rw [Matrix.GeneralLinearGroup.mem_smul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    induction' hy using Submodule.span_induction with x hx x y _ _ hx hy a x _ hx
    · obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      use i
      simp [LinearMap.GeneralLinearGroup.toLinearEquiv, Matrix.mulVecLin]
    · simp
    · simp only [Matrix.mulVec_add]
      exact Submodule.add_mem _ hx hy
    · simpa only [Subring.smul_def, Matrix.mulVec_smul] using Submodule.smul_mem _ a hx
end Basis
