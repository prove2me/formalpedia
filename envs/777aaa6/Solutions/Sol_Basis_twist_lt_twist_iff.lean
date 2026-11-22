-- Prove2me | solution 1 for Basis.twist_lt_twist_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:18:44.005349+00:00
-- url     : https://prove2.me/submissions/6754af00-e4fe-4fe1-b983-2b74d3e5321d

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Basis_twist_le_twist_iff
import Theorems.Thm_Basis_twist_eq_twist_iff
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
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
open BigOperators
namespace Basis
theorem _root_.solution [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f g : ι → ℤ) :
    (b.twist hϖ f).toSubmodule (R := R) < (b.twist hϖ g).toSubmodule (R := R) ↔
      g ≤ f ∧ ∃ i, g i < f i := by
  constructor
  · intro h
    have hgf : g ≤ f := by
      rw [← b.twist_le_twist_iff hϖ]
      apply le_of_lt
      exact h
    by_contra hnotlt
    simp only [not_and, not_exists, not_lt] at hnotlt
    have hfg : f ≤ g := hnotlt hgf
    have : f = g := le_antisymm hfg hgf
    rw [this] at h
    simp at h
  · intro h
    rw [← b.twist_le_twist_iff hϖ] at h
    apply lt_of_le_of_ne h.left
    by_contra heq
    rw [b.twist_eq_twist_iff] at heq
    simp [heq] at h
end Basis
