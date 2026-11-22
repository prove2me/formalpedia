-- Prove2me | solution 1 for BruhatTits.isSimpleChain_of_isTrail_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:23:51.454274+00:00
-- url     : https://prove2.me/submissions/236d12c5-c799-4f6c-9edc-22ce51183f27

import Definitions.Def_BruhatTits_Graph_GroupAction
import Definitions.Def_BruhatTits_Graph_Tree
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
import Theorems.Thm_List_smul_lattice_length
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
open BruhatTits
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) (l : List (BruhatTits.Lattice R)) (hl : l.map (fun L ↦ ⟦L⟧) = p.support) :
    (List.zipWith₃ (fun L₁ _ L₃ ↦ ¬ Lattice.IsSimilar R L₁ L₃) l l.tail l.tail.tail).Forall id := by
  set_option backward.isDefEq.respectTransparency false in
    match p, l with
    | .nil, [L] => simp [List.zipWith₃]
    | .cons _ .nil, [_, _] => simp [List.zipWith₃]
    | .cons adj (.cons adj' .nil), [M, L, Q] =>
        simp only [List.map_cons, List.map_nil, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.cons.injEq, and_true] at hl
        simp only [List.tail_cons, List.zipWith₃, List.forall_cons, id_eq, List.Forall, and_true]
        intro h
        have : (⟦M⟧ : Vertices R) = ⟦Q⟧ := Quotient.sound h
        simp only [SimpleGraph.Walk.cons_isTrail_iff, SimpleGraph.Walk.IsTrail.nil,
          SimpleGraph.Walk.edges_nil, List.not_mem_nil, not_false_eq_true, and_self,
          SimpleGraph.Walk.edges_cons, List.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
          Prod.swap_prod_mk, and_true, not_or, not_and, true_and] at hp
        apply hp.right
        rw [← hl.left, ← hl.right.right]
        exact this
    | .cons adj (.cons adj' <| .cons adj'' q), (L₁ :: L₂ :: L₃ :: l) =>
        simp only [List.map_cons, SimpleGraph.Walk.support_cons, List.cons.injEq] at hl
        simp only [SimpleGraph.Walk.cons_isTrail_iff, SimpleGraph.Walk.edges_cons, List.mem_cons,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true, not_or, not_and] at hp
        simp only [List.tail_cons, List.zipWith₃, List.forall_cons, id_eq]
        refine ⟨?_, ?_⟩
        · intro h
          have h1 := hl.left
          subst h1
          have h2 := hl.right.left
          subst h2
          have h3 := hl.right.right.left
          subst h3
          have h' : (⟦L₁⟧ : Vertices R) = ⟦L₃⟧ := by
            apply Quotient.sound
            exact h
          tauto
        · apply solution (.cons adj' <| .cons adj'' q)
          · simp
            tauto
          · simp
            tauto
end BruhatTits
