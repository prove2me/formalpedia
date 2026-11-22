-- Prove2me | Definitions.Def_BruhatTits_Lattice_Transvect
-- name    : BruhatTits_Lattice_Transvect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:37:13.814316+00:00
-- url     : https://prove2.me/theorems/13d56781-97cc-4195-92d2-07c6d4543a19
-- title:
--   Transvect
-- statement:
--   Definitions and structural lemmas for Transvect, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_toLin_symm_apply
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_swap__apply__280e1e1cec15
import Theorems.Thm_P2M_Basis_swap__apply__cd04b6b0ed1e
import Theorems.Thm_P2M_Basis_swap__symm_e7ab2aa72738
import Theorems.Thm_P2M_Basis_swap_apply__293cd211b0be
import Theorems.Thm_P2M_Basis_swap_apply__dc9b61a54bcb
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] Basis.restrictToLattice_apply
attribute [local simp] Basis.restrict_apply
attribute [local simp] Basis.smulGL_apply
attribute [local simp] Basis.toLinear_symm_ofLinearEquiv_mulVec
attribute [local simp] GL.coe_map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_one
attribute [local simp] LinearMap.GeneralLinearGroup.coe_ofLinearEquiv_bruhat2024
attribute [local simp] Matrix.BlockTriangular.fin_two_iff
attribute [local simp] Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
attribute [local simp] Matrix.GeneralLinearGroup.toLin_symm_apply
attribute [local simp] P2M_Basis_smul__apply_df6e729461ee
attribute [local simp] P2M_Basis_swap__apply__280e1e1cec15
attribute [local simp] P2M_Basis_swap__apply__cd04b6b0ed1e
attribute [local simp] P2M_Basis_swap__symm_e7ab2aa72738
attribute [local simp] P2M_Basis_swap_apply__293cd211b0be
attribute [local simp] P2M_Basis_swap_apply__dc9b61a54bcb
attribute [local simp] P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul
attribute [local simp] map_subtype_smul_standard_eq_standard
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
noncomputable def Basis.transvect (b : Basis (Fin 2) K V) (x : K) : Basis (Fin 2) K V :=
  let v : Fin 2 → V
    | 0 => b 0
    | 1 => x • b 0 + b 1
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← b.span_eq]
    intro a ha
    induction' ha using Submodule.span_induction with x hx x y _ _ hx hy a x _ hx
    · obtain ⟨i, rfl⟩ := hx
      match i with
      | 0 => apply Submodule.subset_span; use 0
      | 1 =>
      rw [show b 1 = v 1 - x • v 0 by simp [v]]
      apply Submodule.sub_mem
      · apply Submodule.subset_span; use 1
      · apply Submodule.smul_mem
        apply Submodule.subset_span; use 0
    · simp
    · exact Submodule.add_mem _ hx hy
    · exact Submodule.smul_mem _ a hx
  have hli : LinearIndependent K v := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    exact (Module.finrank_eq_card_basis b).symm
  Basis.mk hli hsp
variable {R : Subring K}
noncomputable def Basis.transvect' (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    Basis (Fin 2) K (Fin 2 → K) :=
  b.transvect x
noncomputable def Basis.transvectEquiv (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  Basis.equiv b (b.transvect' x) (Equiv.refl _)
noncomputable
def Basis.unipotent (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.toLin.symm <| .ofLinearEquiv (b.transvectEquiv x)
variable [IsDiscreteValuationRing R]


