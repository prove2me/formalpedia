-- Prove2me | solution 1 for BruhatTits.smul_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:30.041181+00:00
-- url     : https://prove2.me/submissions/b18dc0f7-9c75-4e3c-9bf0-45e09f35c11c

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Theorems.Thm_BruhatTits_smul_le_iff
import Theorems.Thm_BruhatTits_smul_eq_iff
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
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
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace BruhatTits
theorem _root_.solution (g : GL ι K) (M L : Submodule R (ι → K)) : g • M < g • L ↔ M < L := by
  constructor
  · intro h
    by_contra hnotlt
    simp [eq_of_le_of_not_lt ((smul_le_iff g).mp (le_of_lt h)) hnotlt] at h
  · intro h
    by_contra hnotlt
    have := eq_of_le_of_not_lt ((smul_le_iff g).mpr (le_of_lt h)) hnotlt
    rw [smul_eq_iff] at this
    simp [this] at h
end BruhatTits
