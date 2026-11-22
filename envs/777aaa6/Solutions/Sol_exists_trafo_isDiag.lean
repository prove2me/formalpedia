-- Prove2me | solution 1 for exists_trafo_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:38:50.067291+00:00
-- url     : https://prove2.me/submissions/406b5fcf-896a-49de-90b6-02fc7a9eddd8

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_monotone_of_isBlockMonotoneDiag
import Theorems.Thm_exists_trafo_isDiag_induction_step
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_coeffs_sup_reindex
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
theorem _root_.solution (g : Matrix (Fin k) (Fin k) K) :
    ∃ (k₁ k₂ : GL (Fin k) R),
    IsMonotoneDiag (n := Fin k) (R := R) (k₁.val * g * k₂.val) ∧
    (k₁.val * g * k₂.val).coeffs_sup v = g.coeffs_sup v := by
  induction k using PNat.recOn with
  | one =>
      refine ⟨1, 1, ?_⟩
      have : Subsingleton (Fin (1 : ℕ+)) := inferInstanceAs (Subsingleton (Fin 1))
      have hm : ((1 : Matrix (Fin (1 : ℕ+)) (Fin (1 : ℕ+)) R).map R.subtype) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      simp only [Units.val_one, hm, one_mul, mul_one]
      exact ⟨⟨isDiag_of_subsingleton g, Subsingleton.monotone _⟩, True.intro⟩
  | succ n ih =>
      let e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fin.succ_equiv_unit n
      let g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
        Matrix.reindex e e g
      obtain ⟨k₁', k₂', hk, hc⟩ := exists_trafo_isDiag_induction_step g' ih
      use GL.reindex e.symm k₁'
      use GL.reindex e.symm k₂'
      convert_to IsMonotoneDiag (n := Fin (n + 1)) (R := R)
          (Matrix.reindex e.symm e.symm (k₁'.val * g' * k₂'.val)) ∧
          (Matrix.reindex e.symm e.symm ((k₁'.val : Matrix _ _ K) * g' * (k₂'.val : Matrix _ _ K))).coeffs_sup v
            = g.coeffs_sup v
      · simp only [PNat.add_coe, PNat.val_ofNat, GL.val_reindex, reindex_apply, Equiv.symm_symm, g']
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_map, Matrix.submatrix_map, Matrix.submatrix_submatrix]
        simp
        rfl
      · simp only [PNat.add_coe, PNat.val_ofNat, GL.val_reindex, reindex_apply, Equiv.symm_symm, g']
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_mul _ _ e e e e.bijective]
        rw [Matrix.submatrix_map, Matrix.submatrix_map, Matrix.submatrix_submatrix]
        simp
        rfl
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp only [reindex_apply, Equiv.symm_symm]
          apply IsDiag.submatrix hk.isDiag (Equiv.injective e)
        · simp only [reindex_apply, Equiv.symm_symm, submatrix_apply]
          apply monotone_of_isBlockMonotoneDiag _ hk
        · simp only [g', coeffs_sup_reindex, hc]
          rfl
