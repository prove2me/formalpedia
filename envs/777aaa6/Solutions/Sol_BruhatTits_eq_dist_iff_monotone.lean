-- Prove2me | solution 1 for BruhatTits.eq_dist_iff_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:55:21.958075+00:00
-- url     : https://prove2.me/submissions/7ac827d9-0e9e-4cc9-9bbd-a63df6ea1258

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_eq_dist_iff
import Theorems.Thm_Fin_rev_antitone
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
theorem _root_.solution (M L : BruhatTits.Lattice R) (n : ℕ) :
    dist M L = n ↔ ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M)
      (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Monotone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 1 - f 0 = n := by
  rw [eq_dist_iff]
  constructor
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    use ϖ, bM.reindex Fin.revPerm, bL.reindex Fin.revPerm, f ∘ Fin.revPerm
    refine ⟨hϖ, ?_, fun i ↦ ?_, ?_⟩
    · exact hf.comp (Fin.rev_antitone 2)
    · simp only [Basis.coe_reindex, Fin.revPerm_symm, Function.comp_apply, Fin.revPerm_apply]
      exact hi i.rev
    · simpa
  · intro ⟨ϖ, bM, bL, f, hϖ, hf, hi, hn⟩
    use ϖ, bM.reindex Fin.revPerm, bL.reindex Fin.revPerm, f ∘ Fin.revPerm
    refine ⟨hϖ, ?_, fun i ↦ ?_, ?_⟩
    · exact hf.comp_antitone (Fin.rev_antitone 2)
    · simp only [Basis.coe_reindex, Fin.revPerm_symm, Function.comp_apply, Fin.revPerm_apply]
      exact hi i.rev
    · simpa
end BruhatTits
