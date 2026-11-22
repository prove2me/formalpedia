-- Prove2me | solution 1 for exists_trafo_isDiag_induction_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:34:22.387101+00:00
-- url     : https://prove2.me/submissions/c05bc443-b26d-4e0a-82e3-bf2ef74f0f23

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_exists_trafo_isNormalBlock
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_coeffs_sup_fromBlocks
import Theorems.Thm_Matrix_coeffs_sup_unique
import Theorems.Thm_Matrix_coeffs_sup_zero
import Theorems.Thm_P2M_Matrix_coeffs_sup_toBlock___le_coeffs_sup_ffc25748b245
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
theorem _root_.solution (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K)
    (ih : ∀ (h : Matrix (Fin k) (Fin k) K), ∃ (k₁ k₂ : GL (Fin k) R),
      IsMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * h * (k₂.val : Matrix _ _ K)).coeffs_sup v = h.coeffs_sup v) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    IsBlockMonotoneDiag (R := R) ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)) ∧
      ((k₁.val : Matrix _ _ K) * g * (k₂.val : Matrix _ _ K)).coeffs_sup v = g.coeffs_sup v := by
  obtain ⟨h₁, h₂, hh, hvc⟩ := exists_trafo_isNormalBlock (R := R) g
  let g' : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K :=
    (h₁.val : Matrix _ _ K) * g * (h₂.val : Matrix _ _ K)
  let h : Matrix (Fin k) (Fin k) K := toBlocks₁₁ g'
  obtain ⟨l₁, l₂, hl, hv⟩ := ih h
  let l₁' : GL (Fin k ⊕ Unit) R := GL.diagonalBlocks l₁ 1
  let l₂' : GL (Fin k ⊕ Unit) R := GL.diagonalBlocks l₂ 1
  use l₁' * h₁
  use h₂ * l₂'
  simp only [Units.val_mul, Matrix.map_mul]
  have he : g' = Matrix.fromBlocks h 0 0 (fun _ _ ↦ (g' (Sum.inr ()) (Sum.inr ()))) := by
    rw [Matrix.ext_iff_blocks]
    simp only [toBlocks_fromBlocks₁₁, hh.isTwoBlockDiagonal.left, toBlocks_fromBlocks₁₂,
      hh.isTwoBlockDiagonal.right, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, true_and, g', h]
    rfl
  convert_to IsBlockMonotoneDiag (R := R) ((l₁'.val : Matrix _ _ K) * g' * (l₂'.val : Matrix _ _ K))
    ∧ ((l₁'.val : Matrix _ _ K) * g' * (l₂'.val : Matrix _ _ K)).coeffs_sup v = g.coeffs_sup v
  · simp only [g']
    group
  · simp only [g']
    group
  · rw [he]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one]
      apply Matrix.IsDiag.fromBlocks hl.isDiag
      · apply isDiag_of_subsingleton
    · intro i j hij
      simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one,
        fromBlocks_apply₁₁]
      apply hl.monotone hij
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simp only [map_zero, Matrix.map_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul,
        _root_.map_one, Matrix.map_one, Matrix.mul_one, one_mul, zero_add, mul_one,
        fromBlocks_apply₂₂]
      simp only [g', hh.monotone, coeffs_sup_fromBlocks, coeffs_sup_zero]
      simp only [ge_iff_le, zero_le', sup_of_le_left]
      rw [hv, coeffs_sup_unique (n := Unit)]
      simp only [hh.monotone, ge_iff_le, coeffs_sup_toBlock₁₁_le_coeffs_sup, sup_of_le_right, h, g']
    · simp only [GL.val_diagonalBlocks, Units.val_one, l₁', l₂']
      rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
        Matrix.fromBlocks_multiply]
      simpa [coeffs_sup_fromBlocks, coeffs_sup_zero, hv, coeffs_sup_unique (n := Unit), g',
        hh.monotone, coeffs_sup_toBlock₁₁_le_coeffs_sup, h]
