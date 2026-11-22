-- Prove2me | solution 1 for Basis.smul_pow_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:25:05.142635+00:00
-- url     : https://prove2.me/submissions/72411929-a2df-4892-8196-5549a04da8cd

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
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
attribute [local simp] Basis.smul'_apply

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι]
open Pointwise
namespace Basis
theorem _root_.solution (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) (k : ℤ) :
    ϖ.val ^ k • (b.twist hϖ f).toSubmodule (R := R) = (b.twist hϖ (f + k)).toSubmodule := by
  simp only [toSubmodule, Submodule.smul_span]
  congr
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    simp only [Pi.intCast_def, Int.cast_id, twist_apply, Set.mem_range, Pi.add_apply]
    use i
    rw [zpow_add₀]
    simp only [mul_comm, smul_smul]
    simpa using hϖ.ne_zero
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    simp only [Pi.intCast_def, Int.cast_id, twist_apply, Pi.add_apply]
    refine ⟨b.twist hϖ f y, ?_, ?_⟩
    exact Set.mem_range_self y
    rw [zpow_add₀]
    · simp [Subring.smul_def, smul_smul, mul_comm]
    · simpa using hϖ.ne_zero
end Basis
