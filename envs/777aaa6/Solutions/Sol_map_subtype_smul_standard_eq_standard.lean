-- Prove2me | solution 1 for map_subtype_smul_standard_eq_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:34:39.113244+00:00
-- url     : https://prove2.me/submissions/4d5cc152-a876-4f71-8602-08702c9723a2

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
import Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
import Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
import Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
import Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
import Theorems.Thm_Lattice_standard_M
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
attribute [local simp] Basis.toLinear_symm_ofLinearEquiv_mulVec
attribute [local simp] Basis.swap₂_apply₀
attribute [local simp] Basis.swap₂_apply₁
attribute [local simp] Basis.swap₂_symm
attribute [local simp] Basis.swap_apply₀
attribute [local simp] Basis.swap_apply₁

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
theorem _root_.solution (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map R.subtype g • Lattice.standard R = Lattice.standard R := by
  ext : 1
  rw [Lattice.smul_M, Lattice.standard_M, Matrix.GeneralLinearGroup.smul_def]
  simp only [Matrix.GeneralLinearGroup.val_map_apply, Subring.coe_subtype]
  have (x : Fin 2 → R) :
      (g.val.map Subtype.val).mulVec (((Algebra.linearMap (↥R) K).compLeft (Fin 2)) x) =
        (Algebra.linearMap (↥R) K).compLeft (Fin 2) (g.val.mulVec x) := by
    induction x using Pi.single_induction with
    | zero => simp
    | add a b ha hb => simp [ha, hb, Matrix.mulVec_add]
    | single i r =>
      have : ((Algebra.linearMap (↥R) K).compLeft (Fin 2)) (Pi.single i r) = Pi.single i r.val := by
        ext
        simp [Algebra.algebraMap_ofSubring_apply, Pi.single_apply]
      simp only [this, Matrix.mulVec_single, op_smul_eq_smul, map_smul]
      rfl
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    rintro - ⟨x, rfl⟩
    simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
      LinearMap.mem_range]
    use g.val.mulVec x
    ext i
    simp [Algebra.algebraMap_ofSubring_apply, this]
  · rintro - ⟨x, rfl⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_restrictScalars,
      Matrix.mulVecLin_apply, exists_exists_eq_and]
    use g.inv.mulVec x
    simp [this]
