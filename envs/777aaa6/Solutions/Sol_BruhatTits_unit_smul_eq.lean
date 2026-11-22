-- Prove2me | solution 1 for BruhatTits.unit_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:00:42.163368+00:00
-- url     : https://prove2.me/submissions/c3586aa1-a2cf-4db7-9a4d-709d14df950b

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
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
import Theorems.Thm_cartanDiag_zero
import Theorems.Thm_conj_cartanDiag_one_one
import Theorems.Thm_conj_cartanDiag_one_zero
import Theorems.Thm_conj_cartanDiag_zero_one
import Theorems.Thm_conj_cartanDiag_zero_zero
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
attribute [local simp] cartanDiag_zero
attribute [local simp] conj_cartanDiag_one_one
attribute [local simp] conj_cartanDiag_one_zero
attribute [local simp] conj_cartanDiag_zero_one
attribute [local simp] conj_cartanDiag_zero_zero
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] BruhatTits.dist_self
attribute [local simp] BruhatTits.mulBasisScalar_apply

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
open Pointwise
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
namespace BruhatTits
theorem _root_.solution (u : Rˣ) (M : BruhatTits.Lattice R) : (Units.map R.subtype u : Kˣ) • M = M := by
  ext x
  constructor
  · intro hx
    simp only [Lattice.smul_module] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype,
      DistribSMul.toLinearMap_apply]
    exact Submodule.smul_mem _ u.val hy
  · intro hx
    simp only [Lattice.smul_module]
    refine ⟨u⁻¹ • x, ?_, ?_⟩
    · exact Submodule.smul_mem _ u.inv hx
    · simp only [Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype, LinearMap.map_smul_of_tower,
        DistribSMul.toLinearMap_apply]
      rw [← Subring.smul_def, Units.smul_def, smul_smul]
      simp
end BruhatTits
