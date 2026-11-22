-- Prove2me | solution 1 for BruhatTits.stabilizer_fun_mk_eq_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:31:59.627431+00:00
-- url     : https://prove2.me/submissions/341dd1a5-9eb4-492a-a0c4-7f3b33f12a66

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_Lattice_valuation_det_eq_one_of_mem_stabilizer
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_Lattice_embDiagonal_smul_eq_smul
import Theorems.Thm_BruhatTits_Lattice_smul_isSimilar
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_BruhatTits_unit_smul_eq
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GL_isMulCentral_diagonal
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulCentral_embDiagonal
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
import Theorems.Thm_valuation_eq_iff
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
attribute [local simp] List.smul_lattice_length
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



set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Matrix GeneralLinearGroup
namespace BruhatTits
theorem _root_.solution {ι : Type*} (L : ι → BruhatTits.Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (fun i ↦ Vertices.mk (L i)) =
      (embDiagonal K (Fin 2)).range ⊔
        MulAction.stabilizer (GL (Fin 2) K) L := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have (i : ι) : ∃ (u : Kˣ), (g * embDiagonal _ _ u) • L i = L i := by
      simp only [MulAction.mem_stabilizer_iff] at hg
      rw [funext_iff] at hg
      replace hg : ⟦g • L i⟧ = ⟦L i⟧ := hg i
      rw [Quotient.eq] at hg
      obtain ⟨u, hu⟩ := hg
      use u
      rwa [← (isMulCentral_embDiagonal u).comm, SemigroupAction.mul_smul,
        Lattice.embDiagonal_smul_eq_smul]
    choose u hu using this
    have hval (i : ι) : v ((g * (embDiagonal K (Fin 2)) (u i))).det = 1 :=
      (L i).valuation_det_eq_one_of_mem_stabilizer _ (hu i)
    simp only [embDiagonal_apply, map_mul, Units.val_mul, val_det_apply, «GL».val_diagonal,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow] at hval
    obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι
    · apply Subgroup.mem_sup_right
      ext i : 1
      exact h.elim i
    · have : g = (embDiagonal K (Fin 2) (u i))⁻¹ * (g * embDiagonal K (Fin 2) (u i)) := by
        rw [← mul_assoc, IsMulCentral.right_comm, inv_mul_cancel, one_mul]
        exact Matrix.GL.isMulCentral_diagonal _
      rw [this]
      refine Subgroup.mul_mem_sup (Subgroup.inv_mem _ ?_) ?_
      · use u i
      · ext j : 1
        rw [← hu, SemigroupAction.mul_smul, SemigroupAction.mul_smul, Lattice.embDiagonal_smul_eq_smul,
          Pi.smul_apply, Pi.smul_apply, Lattice.embDiagonal_smul_eq_smul]
        have hval : v (u i) = v (u j) := by
          have := hval i
          rw [← hval j] at this
          rwa [mul_right_inj', pow_left_inj₀] at this
          · simp
          · simp
          · simp
          · simpa using det_ne_zero g
        rw [valuation_eq_iff] at hval
        obtain ⟨a, ha⟩ := hval
        have : u i = u j * Units.map R.subtype a := by ext; simp [← ha, mul_comm]
        rw [this, SemigroupAction.mul_smul, unit_smul_eq]
  · rw [sup_le_iff]
    refine ⟨?_, fun x (h : x • L = L) ↦ ?_⟩
    · rintro - ⟨u, rfl⟩
      ext i
      show ⟦_⟧ = _
      rw [Lattice.embDiagonal_smul_eq_smul, Quotient.eq]
      exact Lattice.smul_isSimilar _ _ _
    · rw [MulAction.mem_stabilizer_iff]
      simp_rw [funext_iff, Pi.smul_apply] at h
      ext i
      show ⟦_⟧ = _
      rw [h i]
end BruhatTits
