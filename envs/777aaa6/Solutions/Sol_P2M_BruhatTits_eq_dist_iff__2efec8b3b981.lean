-- Prove2me | solution 1 for P2M_BruhatTits_eq_dist_iff__2efec8b3b981
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:55:22.356591+00:00
-- url     : https://prove2.me/submissions/98a465c4-c12a-46fc-a8f1-72e16be1c49e

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_eq_dist_iff
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



set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (a b : ℤ), Irreducible ϖ ∧
         b ≤ a ∧ bL 0 = ϖ.val ^ a • (bM 0).val ∧ bL 1 = ϖ.val ^ b • (bM 1).val ∧ a - b = n := by
  rw [eq_dist_iff]
  constructor
  · rintro ⟨ϖ, bM, bL, f, hϖ, _, hrep, hdiff⟩
    refine ⟨ϖ, bM, bL, f 0, f 1, hϖ, Int.le.intro_sub n hdiff, hrep 0, hrep 1, hdiff⟩
  · rintro ⟨ϖ, bM, bL, a, b, hϖ, hle, h0, h1, hdiff⟩
    let f (i : Fin 2) : ℤ := match i with
      | 0 => a
      | 1 => b
    refine ⟨ϖ, bM, bL, f, hϖ, ?_, ?_, hdiff⟩
    · intro i j hij
      match i, j with
      | 0, 0 => rfl
      | 0, 1 => exact hle
      | 1, 0 => simp at hij
      | 1, 1 => rfl
    · intro i
      match i with
      | 0 => exact h0
      | 1 => exact h1
end BruhatTits
