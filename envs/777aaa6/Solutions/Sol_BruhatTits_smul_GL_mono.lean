-- Prove2me | solution 1 for BruhatTits.smul_GL_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:50:43.176009+00:00
-- url     : https://prove2.me/submissions/ed035c5a-6355-461b-aa97-138c524c5623

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
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
theorem _root_.solution {M L : Submodule R (ι → K)} (g : GL ι K) (hML : M ≤ L) : g • M ≤ g • L := by
  intro x
  simp only [Matrix.GeneralLinearGroup.mem_smul, forall_exists_index, and_imp]
  rintro y hy rfl
  use y, (hML hy)
end BruhatTits
