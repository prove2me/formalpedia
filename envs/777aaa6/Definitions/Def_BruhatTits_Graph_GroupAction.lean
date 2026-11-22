-- Prove2me | Definitions.Def_BruhatTits_Graph_GroupAction
-- name    : BruhatTits_Graph_GroupAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:21:21.504567+00:00
-- url     : https://prove2.me/theorems/27525a1e-ce96-4346-9875-0597f29b7a3d
-- title:
--   Group Action
-- statement:
--   Definitions and structural lemmas for Group Action, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_Lattice_isSimilar_smul
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
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_smul
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
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
namespace BruhatTits
section Action
lemma isSimilar_smul_of_isSimilar (g : GL (Fin 2) K) (L M : BruhatTits.Lattice R) (h : L.IsSimilar R M) :
    (g • L).IsSimilar R (g • M) := by
  obtain ⟨a, rfl⟩ := h
  have : g • a • L = a • g • L := by
    apply Lattice.ext
    simp only [Lattice.smul_M, Lattice.smul_module, Units.smul_def]
    ext x
    simp only [Matrix.GeneralLinearGroup.mem_smul]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simp only [DistribSMul.toLinearMap_apply, Matrix.mulVec_smul]
      refine ⟨g.val.mulVec z, ?_, rfl⟩
      simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul]
      use z, hz
    · rintro ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨a.val • z, ?_, ?_⟩
      · use z, hz
        rfl
      · simp [Matrix.mulVec_smul]
  rw [this]
  exact Lattice.isSimilar_smul R (g • L) a
def smulGL (g : GL (Fin 2) K) : Vertices R → Vertices R :=
  Quotient.lift (fun L ↦ ⟦g • L⟧) <| by
    intro L M h
    apply Quotient.sound
    exact isSimilar_smul_of_isSimilar g L M h
lemma smulGL_mk (g : GL (Fin 2) K) (L : BruhatTits.Lattice R) :
    smulGL g ⟦L⟧ = ⟦g • L⟧ :=
  rfl
instance : SMul (GL (Fin 2) K) (Vertices R) where
  smul := smulGL
lemma Vertices.smul_def (g : GL (Fin 2) K) (x : Vertices R) :
    g • x = smulGL g x :=
  rfl
instance : MulAction (GL (Fin 2) K) (Vertices R) where
  one_smul x := by
    refine Quotient.inductionOn x (fun L ↦ ?_)
    rw [Vertices.smul_def, smulGL_mk, one_smul]
  mul_smul g h x := by
    refine Quotient.inductionOn x (fun L ↦ ?_)
    rw [Vertices.smul_def, smulGL_mk]
    rw [mul_smul]
    rw [← smulGL_mk, ← Vertices.smul_def]
    rw [← smulGL_mk, ← Vertices.smul_def]
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
instance : MulAction.IsPretransitive (GL (Fin 2) K) (Vertices R) where
  exists_smul_eq L M := by
    classical
    induction' L using Quotient.inductionOn with L
    induction' M using Quotient.inductionOn with M
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL (Fin 2) K) L M
    use g
    rfl
@[simp]
lemma inv_smul_smul_eq_inv (g : GL (Fin 2) K) (x y : Vertices R) :
    inv (g • x) (g • y) = inv x y := by
  refine Quotient.inductionOn₂ x y (fun L M ↦ ?_)
  rw [Vertices.smul_def, smulGL_mk]
  rw [Vertices.smul_def, smulGL_mk]
  show dist (g • L) (g • M) = dist L M
  simp
@[simp]
lemma adj_smul_smul_iff_adj (g : GL (Fin 2) K) (x y : Vertices R) :
    BTgraph.Adj (g • x) (g • y) ↔ BTgraph.Adj x y := by
  show inv (g • x) (g • y) = 1 ↔ inv x y = 1
  simp
def _root_.Matrix.GeneralLinearGroup.toGraphIso (g : GL (Fin 2) K) :
    BTgraph (R := R) ≃g BTgraph (R := R) where
  toEquiv := MulAction.toPerm g
  map_rel_iff' {x y} := by simp
instance : GraphAction (GL (Fin 2) K) (BTgraph (R:= R)) where
  smul_adj_smul g x y := (adj_smul_smul_iff_adj g x y).mpr


