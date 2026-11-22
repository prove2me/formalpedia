-- Prove2me | solution 1 for BruhatTits.signature_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:48:21.177173+00:00
-- url     : https://prove2.me/submissions/a9cafdd5-fb2d-48a7-9264-b02b6f635c5f

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
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
import Theorems.Thm_cartan_decomposition_unique_uniformizer
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
theorem _root_.solution {M L : BruhatTits.Lattice R}
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {bM bM' : Basis (Fin 2) R M.M} {bL bL' : Basis (Fin 2) R L.M}
    {f f' : Fin 2 → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val)
    (h' : ∀ i, (bL' i).val = (ϖ' ^ f' i : K) • (bM' i).val) :
    f = f' := by
  obtain ⟨⟨k₁⟩, hk₁⟩ := MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ)
    bM bM'
  obtain ⟨⟨k₂⟩, hk₂⟩ := MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ)
    bL bL'
  let d : GL (Fin 2) K := cartanDiag (k := 2) ϖ hϖ f
  have hd : bL.toGL = bM.toGL * d := by
    ext i j
    simp only [Basis.toGL_apply, Units.val_mul, val_cartanDiag, PNat.val_ofNat, mul_diagonal, d]
    rw [mul_comm, h j]
    simp
  let d' : GL (Fin 2) K := cartanDiag (k := 2) ϖ' hϖ' f'
  have hd' : bL'.toGL = bM'.toGL * d' := by
    ext i j
    simp only [Basis.toGL_apply, Units.val_mul, val_cartanDiag, PNat.val_ofNat, mul_diagonal, d']
    rw [mul_comm, h' j]
    simp
  have hbMd' : bM'.toGL * d' = bM.toGL * d * k₂ := by
    rw [← hd', ← hk₂]
    erw [basis_smul_toGL, hd]
  have hbM : bM.toGL = bM'.toGL * k₁⁻¹ := by
    rw [← hk₁]
    erw [basis_smul_toGL k₁ bM]
    rw [mul_assoc, GL.map_mul_map_inv, mul_one]
  have : (1 : GL (Fin 2) R) * d' * (1 : GL (Fin 2) R) = k₁⁻¹ * d * k₂ := by
    calc (1 : GL (Fin 2) R) * d' * (1 : GL (Fin 2) R) = bM'.toGL⁻¹ * (bM'.toGL * d') :=
        by rw [GL.map_one]; group
                  _ = bM'.toGL⁻¹ * bM.toGL * d * k₂ := by rw [hbMd']; group
                  _ = bM'.toGL⁻¹ * bM'.toGL * k₁⁻¹ * d * k₂ := by rw [hbM]; group
                  _ = k₁⁻¹ * d * k₂ := by group
  apply cartan_decomposition_unique_uniformizer (k := 2) hϖ hϖ' hf hf'
    (k₁ := k₁⁻¹) (k₂ := k₂) (k₁' := 1) (k₂' := 1)
    this.symm
end BruhatTits
