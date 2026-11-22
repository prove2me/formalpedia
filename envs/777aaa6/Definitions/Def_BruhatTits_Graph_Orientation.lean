-- Prove2me | Definitions.Def_BruhatTits_Graph_Orientation
-- name    : BruhatTits_Graph_Orientation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:22:23.885183+00:00
-- url     : https://prove2.me/theorems/b18f1a8d-52c7-4a98-a41c-3f7dee686a96
-- title:
--   Orientation
-- statement:
--   Definitions and structural lemmas for Orientation, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_BruhatTits_mulBasisScalar_toGL
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_det
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GL_diagonal_det
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
suppress_compilation
namespace BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
namespace Lattice
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
def valuation (L : BruhatTits.Lattice R) : ℤ :=
  zaddVal (R := R) (Matrix.GeneralLinearGroup.det L.basis.toGL)
lemma zaddVal_det_eq_of_basis {L : BruhatTits.Lattice R} (b₁ b₂ : Basis (Fin 2) R L.M) :
    zaddVal (R := R) (Matrix.GeneralLinearGroup.det b₁.toGL) =
      zaddVal (R := R) (Matrix.GeneralLinearGroup.det b₂.toGL) := by
  obtain ⟨⟨g⟩, (h : (MulOpposite.op g) • _ = _)⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ) b₁ b₂
  subst h
  simp only [basis_smul_toGL, map_mul, zaddVal_mul, left_eq_add, GL.map_det]
  simp
def IsEven (L : BruhatTits.Lattice R) : Prop := Even L.valuation
def IsOdd (L : BruhatTits.Lattice R) : Prop := Odd L.valuation
lemma isOdd_iff_notEven (L : BruhatTits.Lattice R) :
    L.IsOdd ↔ ¬ L.IsEven :=
  (Int.not_even_iff_odd).symm
lemma isEven_iff (L : BruhatTits.Lattice R) :
    L.IsEven ↔ ∃ (b : Basis (Fin 2) R L.M),
      Even (zaddVal (R := R) (b.toGL.det)) := by
  refine ⟨fun h ↦ ⟨L.basis, h⟩, fun ⟨b, h⟩ ↦ ?_⟩
  rwa [zaddVal_det_eq_of_basis b L.basis] at h
open Matrix
lemma isEven_smul_of_isEven {L : BruhatTits.Lattice R} (a : Kˣ) (h : L.IsEven) :
    (a • L).IsEven := by
  rw [isEven_iff]
  use (mulBasisScalar a L.basis)
  simp only [mulBasisScalar_toGL, _root_.map_mul, zaddVal_mul]
  refine Even.add ?_ h
  simp [Matrix.GL.diagonal_det, sq]
lemma isEven_smul_iff (L : BruhatTits.Lattice R) (a : Kˣ) :
    (a • L).IsEven ↔ L.IsEven := by
  refine ⟨fun h ↦ ?_, isEven_smul_of_isEven a⟩
  rw [show L = a⁻¹ • a • L by simp]
  exact isEven_smul_of_isEven _ h
lemma isEven_iff_of_isSimilar {M L : BruhatTits.Lattice R} (h : IsSimilar R M L) :
    M.IsEven ↔ L.IsEven := by
  obtain ⟨a, rfl⟩ := h
  rw [isEven_smul_iff]
lemma isOdd_iff_of_isSimilar {M L : BruhatTits.Lattice R} (h : IsSimilar R M L) :
    M.IsOdd ↔ L.IsOdd := by
  rw [isOdd_iff_notEven, isOdd_iff_notEven, not_iff_not]
  exact isEven_iff_of_isSimilar h
end Lattice
section SLAction
instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) K) (BruhatTits.Lattice R) :=
  MulAction.compHom (BruhatTits.Lattice R) Matrix.SpecialLinearGroup.toGL
instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Vertices R) :=
  MulAction.compHom (Vertices R) Matrix.SpecialLinearGroup.toGL
end SLAction
section
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
def IsEven (x : Vertices R) : Prop :=
  Quotient.lift Lattice.IsEven (fun _ _ hML ↦ propext <| Lattice.isEven_iff_of_isSimilar hML) x
def IsOdd (x : Vertices R) : Prop :=
  Quotient.lift Lattice.IsOdd (fun _ _ hML ↦ propext <| Lattice.isOdd_iff_of_isSimilar hML) x
open Classical in
/-- A canonical weight function on the vertices of the BT tree:
Even vertices have weight `1` and odd vertices have weight `-1`. -/
def BTweight (A : Type*) [CommRing A] (x : Vertices R) : Aˣ := if IsEven x then 1 else -1
instance : GraphAction (Matrix.SpecialLinearGroup (Fin 2) K) (BTgraph (R := R)) where
  smul_adj_smul g x y := (adj_smul_smul_iff_adj (Matrix.SpecialLinearGroup.toGL g) x y).mpr
end
end BruhatTits


