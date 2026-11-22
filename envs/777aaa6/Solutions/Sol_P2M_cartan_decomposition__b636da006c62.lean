-- Prove2me | solution 1 for P2M_cartan_decomposition__b636da006c62
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:43:09.493838+00:00
-- url     : https://prove2.me/submissions/5c75f5a2-1131-4ce7-8738-f3623227276e

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_cartan_decomposition
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
theorem _root_.solution [IsDiscreteValuationRing R] (g : GL (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R) (f : Fin k → ℤ),
      Antitone f ∧ k₁ * cartanDiag ϖ hϖ f * k₂ = g := by
  obtain ⟨k₁, k₂, f, hf, hfeq⟩ := cartan_decomposition ϖ hϖ g
  refine ⟨k₁⁻¹, k₂⁻¹, f, hf, ?_⟩
  rw [← hfeq, mul_assoc, mul_assoc, GL.map_mul_map_inv, mul_one, ← mul_assoc, GL.map_inv_mul_map,
    one_mul]
