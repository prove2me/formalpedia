-- Prove2me | solution 1 for P2M_BruhatTits_Lattice_exists_GL_forall_smul_eq_ntwist__of_isSimpleChain_cons_7d5092b8b2af
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:24:01.156284+00:00
-- url     : https://prove2.me/submissions/63f4beed-853d-4a1b-b3e4-e1b3ada9bb6c

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_BruhatTits_exists_trafo_step_one
import Theorems.Thm_P2M_BruhatTits_Lattice_exists_GL_smul_eq_ntwist__of_isSimpleChain_cons_ce39f07d52dd
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
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
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__a337ed21e963
import Theorems.Thm_P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
import Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
import Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
import Theorems.Thm_P2M_Basis_transvect__apply__03ca5877df1c
import Theorems.Thm_P2M_Basis_transvect__apply__1bdd29fda3f2
import Theorems.Thm_P2M_Basis_transvect_apply__3554c878d91a
import Theorems.Thm_P2M_Basis_transvect_apply__c6d95b5429da
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_map_subtype_smul
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
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_unipotent_pow_irred_smul_eq
import Theorems.Thm_zaddVal_mul
import Theorems.Thm_zaddVal_units_map
attribute [local simp] Basis.restrictToLattice_apply
attribute [local simp] Basis.restrict_apply
attribute [local simp] Basis.smulGL_apply
attribute [local simp] Basis.toLinear_symm_ofLinearEquiv_mulVec
attribute [local simp] BruhatTits.dist_self
attribute [local simp] BruhatTits.dist_smul_GL_eq_dist
attribute [local simp] BruhatTits.inv_mk
attribute [local simp] BruhatTits.mulBasisScalar_apply
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
attribute [local simp] P2M_Basis_transvectEquiv_apply__a337ed21e963
attribute [local simp] P2M_Basis_transvectEquiv_apply__b7ef14f0fd7c
attribute [local simp] P2M_Basis_transvectResidue_apply__556496910c93
attribute [local simp] P2M_Basis_transvectResidue_apply__d9f90c0bfc03
attribute [local simp] P2M_Basis_transvect__apply__03ca5877df1c
attribute [local simp] P2M_Basis_transvect__apply__1bdd29fda3f2
attribute [local simp] P2M_Basis_transvect_apply__3554c878d91a
attribute [local simp] P2M_Basis_transvect_apply__c6d95b5429da
attribute [local simp] P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
attribute [local simp] Submodule.comap_subtype_smul
attribute [local simp] Submodule.map_subtype_smul
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
attribute [local simp] map_subtype_smul_standard_eq_standard
attribute [local simp] zaddVal_mul
attribute [local simp] zaddVal_units_map


attribute [local simp] List.smul_lattice_length

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
open IsLocalRing
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
namespace Lattice
theorem _root_.solution (l : List (BruhatTits.Lattice R)) (M : BruhatTits.Lattice R)
    (hMl : (M :: l).IsSimpleChain) (b : Basis (Fin 2) K (Fin 2 → K)) (ϖ : R) (hϖ : Irreducible ϖ)
    (hl : l.zipIdx.Forall (fun (L, n) ↦ L = (b.ntwist₂ hϖ (l.length - n - 1) 0).toLattice)) :
    ∃ (g : GL (Fin 2) K), (M :: l).zipIdx.Forall
      (fun (L, n) ↦ g • L = (b.ntwist₂ hϖ (l.length - n) 0).toLattice) := by
  match l with
  | [] =>
    simp only [List.Forall, List.length_nil, ge_iff_le, le_refl, tsub_eq_zero_of_le]
    apply MulAction.IsPretransitive.exists_smul_eq
  | [L] =>
    simp only [List.length_cons, List.length_nil, zero_add, List.zipIdx_cons, Nat.reduceAdd,
      List.zipIdx_nil, List.Forall, tsub_zero, tsub_self]
    simp only [List.length_cons, List.length_nil, zero_add, tsub_le_iff_right,
      le_add_iff_nonneg_right, zero_le, Nat.sub_eq_zero_of_le, List.zipIdx_cons, List.zipIdx_nil,
      List.forall_cons, List.Forall, and_true] at hl
    rw [hl]
    have : b.ntwist₂ hϖ 0 0 = b := by
      ext i
      fin_cases i <;> simp
    rw [this]
    have hbLM : b.toSubmodule = L.M := by simp [hl, this]
    have hstd : IsStandardNeighbour M L := by simpa [List.Chain', List.isChain_cons_cons] using hMl.isStandardNeighbour
    apply exists_trafo_step_one
    · rw [hbLM]
      exact hstd.lt
    · rw [hbLM]
      exact hstd.ϖlt ϖ hϖ
  | L₁ :: L₂ :: l' =>
    generalize hldef : L₁ :: L₂ :: l' = l at *
    have hlen : 2 ≤ l.length := by simp [← hldef]
    obtain ⟨x, h⟩ := M.exists_GL_smul_eq_ntwist₂_of_isSimpleChain_cons l hlen hMl b ϖ hϖ hl
    use b.unipotent (ϖ ^ (l.length - 1) * x)
    simp only [List.zipIdx_cons, zero_add, List.forall_cons, tsub_zero]
    refine ⟨h, ?_⟩
    dsimp only at hl
    rw [show 1 = 1 + 0 by simp, ← List.map_snd_add_zipIdx_eq_zipIdx]
    simp only [add_zero, List.forall_map_iff]
    show List.Forall (fun (L, n) ↦ b.unipotent (ϖ ^ (l.length - 1) * x) • L =
      (b.ntwist₂ hϖ (l.length - (n + 1)) 0).toLattice) l.zipIdx
    rw [List.forall_iff_forall_mem] at hl ⊢
    intro ⟨L, n⟩ h
    have : l.length - (n + 1) = l.length - n - 1 := by omega
    replace hl := hl (L, n) h
    dsimp only at hl ⊢
    rw [this, hl]
    apply unipotent_pow_irred_smul_eq
    omega
end Lattice
end BruhatTits
