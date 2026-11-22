-- Prove2me | solution 1 for conj_cartanDiag_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:19:40.351353+00:00
-- url     : https://prove2.me/submissions/d97e54f3-98f1-4c96-904c-d9cdcc7a89f3

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_cartanDiag_zero
import Theorems.Thm_conj_cartanDiag_zero_zero
import Theorems.Thm_conj_cartanDiag_one_one
import Theorems.Thm_conj_cartanDiag_one_zero
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GL_conj_diagonal_apply
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


attribute [local simp] cartanDiag_zero
attribute [local simp] conj_cartanDiag_zero_zero
attribute [local simp] conj_cartanDiag_one_one
attribute [local simp] conj_cartanDiag_one_zero

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
local notation "v" => ValuationRing.valuation R K
attribute [-simp] Subring.coe_subtype
open Matrix
variable {k l : ℕ+}
noncomputable section
attribute [-simp] Fin.natCast_eq_last Fin.coe_eq_castSucc
set_option maxHeartbeats 300000
variable (ϖ : R) (hϖ : Irreducible ϖ)
omit [ValuationRing ↥R] [IsFractionRing (↥R) K]
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) (f : Fin 2 → ℤ) :
    MulAut.conj (cartanDiag ϖ hϖ f) g 0 1 = ϖ.val ^ (f 0 - f 1) * g 0 1 := by
  have hn : (ϖ : K) ≠ 0 := by simpa only [ne_eq, Subring.coe_eq_zero_iff] using hϖ.ne_zero
  rw [cartanDiag, Matrix.GL.conj_diagonal_apply]
  change (ϖ : K) ^ f 0 * (ϖ : K) ^ (-f 1) * g 0 1 = (ϖ : K) ^ (f 0 - f 1) * g 0 1
  rw [← zpow_add₀ hn]
  simp only [sub_eq_add_neg]
