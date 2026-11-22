-- Prove2me | solution 1 for exists_normalization_of_isMonotoneDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:20:41.964904+00:00
-- url     : https://prove2.me/submissions/94206ec9-1c73-4288-a255-d9fb92b14566

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_apply_ne_zero_of_isDiag
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_exp_le_exp_of_pow_le_pow
import Theorems.Thm_valuation_lt_one_of_irreducible
import Theorems.Thm_valuation_unit_eq_one
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
include hϖ
theorem _root_.solution [IsDiscreteValuationRing R] (g : GL (Fin k) K)
    (h : IsMonotoneDiag (R := R) g.val) :
    ∃ (d : Fin k → Rˣ) (f : Fin k → ℤ) ,
    Antitone f ∧ ∀ (j : Fin k), (GL.diagonal d * g).val j j = ϖ ^ f j := by
  have (j : Fin k) : ∃ (n : ℤ) (u : Rˣ), g j j = u * ϖ ^ n := by
    apply eq_unit_mul_pow_irreducible ϖ hϖ
    apply g.apply_ne_zero_of_isDiag
    exact h.isDiag
  choose f d hd using this
  use (fun j ↦ (d j)⁻¹)
  use f
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hle : v (g i i) ≤ v (g j j) := h.monotone hij
    rw [hd i, hd j] at hle
    simp [valuation_unit_eq_one] at hle
    apply exp_le_exp_of_pow_le_pow (v ϖ) _ _ hle
    apply valuation_lt_one_of_irreducible ϖ hϖ
    rw [Valuation.ne_zero_iff]
    intro hzero
    rw [Subring.coe_eq_zero_iff] at hzero
    apply Irreducible.ne_zero hϖ hzero
  · intro j
    simp only [GL.map, GL.val_diagonal, RingHom.mapMatrix_apply, map_zero, diagonal_map,
      map_units_inv, Units.inv_eq_val_inv, coe_units_inv, Units.val_mul, diagonal_mul]
    rw [hd j]
    field_simp
    rfl
