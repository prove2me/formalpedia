-- Prove2me | Definitions.Def_BruhatTits_Graph_Regular
-- name    : BruhatTits_Graph_Regular
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T11:24:34.304946+00:00
-- url     : https://prove2.me/theorems/8f81276c-701c-4dfa-ab5c-f0c0b91b94ad
-- title:
--   Regular
-- statement:
--   Definitions and structural lemmas for Regular, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Regular.lean

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_BruhatTits_Graph_Tree
import Theorems.Thm_Basis_restrictToLattice_apply
import Theorems.Thm_Basis_restrict_apply
import Theorems.Thm_Basis_smulGL_apply
import Theorems.Thm_Basis_toLinear_symm_ofLinearEquiv_mulVec
import Theorems.Thm_BruhatTits_dist_self
import Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
import Theorems.Thm_BruhatTits_exists_basis_eq_ntwist_of_isNeighbour
import Theorems.Thm_BruhatTits_inv_mk
import Theorems.Thm_BruhatTits_isNeighbour_of_isStandardNeighbour
import Theorems.Thm_BruhatTits_isNeighbour_symm
import Theorems.Thm_BruhatTits_mulBasisScalar_apply
import Theorems.Thm_BruhatTits_ntwist_isStandardNeighbour
import Theorems.Thm_BruhatTits_unit_smul_eq
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_IsLattice_of_le_of_isLattice_right
import Theorems.Thm_LinearMap_GeneralLinearGroup_coe_ofLinearEquiv_bruhat2024
import Theorems.Thm_List_smul_lattice_length
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_toLin_symm_apply
import Theorems.Thm_P2M_Basis_ntwist__zero_zero_fe200314a2d0
import Theorems.Thm_P2M_Basis_smul__apply_df6e729461ee
import Theorems.Thm_P2M_Basis_smul_ntwist__ee7cf44200ea
import Theorems.Thm_P2M_Basis_smul_pow_twist__3aaeb99ffa1d
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
import Theorems.Thm_P2M_Basis_twist__le_twist__iff_0b153256402b
import Theorems.Thm_P2M_LinearMap_toMatrix__mulVec_bruhat2024_4481c521c4b9
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Submodule_finrank_lt_finrank_of_ne_top
import Theorems.Thm_Submodule_map_subtype_smul
import Theorems.Thm_Submodule_quotient_equiv_eq_bot_iff
import Theorems.Thm_Submodule_zero_lt_finrank_of_ne_bot
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
import Theorems.Thm_ideal_smul_lt_of_ne_bot
import Theorems.Thm_lt_of_ne_top
import Theorems.Thm_map_subtype_smul_standard_eq_standard
import Theorems.Thm_maximalIdeal_smul_eq_uniformizer_smul
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
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
def standardNeighbourBasis {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    Basis (Fin 2) K (Fin 2 → K) :=
  (exists_basis_eq_ntwist_of_isNeighbour L y ((isNeighbour_symm _ _).mp h)).choose
@[simp]
lemma standardNeighbourBasis_toLattice_Eq {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    (standardNeighbourBasis h).toLattice = L :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose_spec.left
def standardNeighbourϖ {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) : R :=
  (exists_basis_eq_ntwist_of_isNeighbour L y ((isNeighbour_symm _ _).mp h)).choose_spec.choose
lemma standardNeighbourϖ_irreducible {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    Irreducible (standardNeighbourϖ h) :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose
def standardNeighbour {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    BruhatTits.Lattice R :=
  ((standardNeighbourBasis h).ntwist₂ (standardNeighbourϖ_irreducible h) 1 0).toLattice
@[simp]
lemma standardNeighbourBasis_ntwist_eq {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    ((standardNeighbourBasis h).ntwist₂ (standardNeighbourϖ_irreducible h) 1 0).toLattice =
      standardNeighbour h :=
  rfl
lemma standardNeighbour_isStandardNeighbour {L : BruhatTits.Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) :
    IsStandardNeighbour (standardNeighbour h) L := by
  nth_rw 2 [← standardNeighbourBasis_toLattice_Eq h]
  apply ntwist_isStandardNeighbour
@[simp]
lemma standardNeighbour_mk_eq {L : BruhatTits.Lattice R} {y : Vertices R} (h : IsNeighbour y ⟦L⟧) :
    ⟦standardNeighbour h⟧ = y :=
  (exists_basis_eq_ntwist_of_isNeighbour L y
    ((isNeighbour_symm _ _).mp h)).choose_spec.choose_spec.choose_spec.right
lemma exists_basis_standardNeighbour_eq_twist {L : BruhatTits.Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      L = b.toLattice ∧ standardNeighbour h = (b.ntwist₂ hϖ 1 0).toLattice := by
  use standardNeighbourϖ h, standardNeighbourϖ_irreducible h, standardNeighbourBasis h
  simp
lemma eq_standardNeighbour_of_isStandardNeighbour {L : BruhatTits.Lattice R} {y : Vertices R}
    (h : IsNeighbour y ⟦L⟧) (M : BruhatTits.Lattice R) (hM : ⟦M⟧ = y)
    (hML : IsStandardNeighbour M L) :
    M = standardNeighbour h := by
  obtain ⟨ϖ, hϖ, b, rfl, hstd⟩ := exists_basis_standardNeighbour_eq_twist h
  have : (⟦M⟧ : Vertices R) = ⟦standardNeighbour h⟧ := by simp [hM]
  have : Lattice.IsSimilar R (standardNeighbour h) M := Quotient.exact this.symm
  obtain ⟨a, rfl⟩ := this
  obtain ⟨n, u, ha⟩ := eq_unit_mul_pow_irreducible' ϖ hϖ a
  rw [ha, mul_comm, mul_smul, unit_smul_eq] at hML ⊢
  rw [hstd] at hML
  nth_rw 2 [← b.ntwist₂_zero_zero hϖ] at hML
  have h1 := hML.lt
  have h2 := hML.ϖlt ϖ hϖ
  rw [Basis.toLattice_module, b.smul_ntwist₂] at h2
  simp only [Lattice.smul_module, Basis.toLattice_module, Units.smul_def,
    Units.val_zpow_eq_zpow_val, Units.val_mk0, Basis.ntwist₂] at h1 h2
  rw [b.smul_pow_twist₂] at h1
  simp at h1
  rw [b.smul_pow_twist₂] at h2
  simp only [zero_add, Nat.cast_one, CharP.cast_eq_zero] at h2
  apply le_of_lt at h1
  apply le_of_lt at h2
  rw [b.twist₂_le_twist₂_iff] at h1 h2
  have : n = 0 := by omega
  rw [this]
  simp
open IsLocalRing
def neighborsEquivStandardNeighbors (L : BruhatTits.Lattice R) :
    { y : Vertices R | IsNeighbour y ⟦L⟧ } ≃ { M : BruhatTits.Lattice R | IsStandardNeighbour M L } where
  toFun y := ⟨standardNeighbour y.property, standardNeighbour_isStandardNeighbour y.property⟩
  invFun M := ⟨⟦M⟧, isNeighbour_of_isStandardNeighbour M.property⟩
  left_inv y := by simp
  right_inv M := by
    ext : 1
    simp only [Set.mem_setOf_eq]
    symm
    apply eq_standardNeighbour_of_isStandardNeighbour
    rfl
    exact M.property
def Lattice.quotientRestrictScalarsEquiv (L : BruhatTits.Lattice R) :
    Submodule (ResidueField R) L.quotient ≃o Submodule R L.quotient where
  toFun M := M.restrictScalars R
  invFun M := {
      toAddSubmonoid := M.toAddSubmonoid
      smul_mem' := fun r _ hx ↦
        Quotient.inductionOn' r (fun r ↦ Submodule.smul_mem _ r hx)
    }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
instance (priority := 99999) (L : BruhatTits.Lattice R) : SMul (Ideal R) (Submodule R L.M) := Submodule.instSMul
def Lattice.submoduleRestrictQuotientEquiv (L : BruhatTits.Lattice R) :
    Submodule R L.quotient ≃o { M : Submodule R L.M // (maximalIdeal R • ⊤ : Submodule R L.M) ≤ M } :=
  Submodule.comapMkQRelIso (maximalIdeal R • ⊤ : Submodule R L.M)
def Lattice.submoduleQuotientEquiv (L : BruhatTits.Lattice R) :
    Submodule (ResidueField R) L.quotient ≃o { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } :=
  L.quotientRestrictScalarsEquiv.trans L.submoduleRestrictQuotientEquiv
lemma submodule_ne_top_of_finrank {L : BruhatTits.Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h : Module.finrank (ResidueField R) M = 1) : M ≠ ⊤ := by
  rintro rfl
  simp only [finrank_top] at h
  have : Module.finrank (ResidueField ↥R) L.quotient = 2 := Lattice.quotient_finrank L
  omega
omit [IsFractionRing R K] in
lemma submodule_ne_bot_of_finrank {L : BruhatTits.Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h : Module.finrank (ResidueField R) M = 1) : M ≠ ⊥ := by
  rintro rfl
  simp at h
lemma submodule_finrank_eq_one_of_ne_bot_of_ne_top {L : BruhatTits.Lattice R}
    {M : Submodule (ResidueField R) L.quotient}
    (h₁ : M ≠ ⊥) (h₂ : M ≠ ⊤) :
    Module.finrank (ResidueField R) M = 1 := by
  have : Module.finrank (ResidueField R) M < 2 := by
    rw [← L.quotient_finrank]
    apply Submodule.finrank_lt_finrank_of_ne_top
    exact h₂
  have : 0 < Module.finrank (ResidueField R) M := by
    apply Submodule.zero_lt_finrank_of_ne_bot
    exact h₁
  omega
lemma submodule_finrank_eq_one_iff {L : BruhatTits.Lattice R}
    {M : Submodule (ResidueField R) L.quotient} :
    Module.finrank (ResidueField R) M = 1 ↔ M ≠ ⊥ ∧ M ≠ ⊤ :=
  ⟨fun h ↦ ⟨submodule_ne_bot_of_finrank h, submodule_ne_top_of_finrank h⟩,
   fun h ↦ submodule_finrank_eq_one_of_ne_bot_of_ne_top h.left h.right⟩
def linesQuotientEquiv (L : BruhatTits.Lattice R) :
    { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } ≃
      { M : { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } // M ≠ ⊥ ∧ M ≠ ⊤ } where
  toFun M := ⟨L.submoduleQuotientEquiv M, by
    set_option backward.isDefEq.respectTransparency false in
      simpa only [ne_eq, map_eq_bot_iff, map_eq_top_iff, ← submodule_finrank_eq_one_iff] using M.property⟩
  invFun M := ⟨L.submoduleQuotientEquiv.symm M, by
    rw [submodule_finrank_eq_one_iff]
    set_option backward.isDefEq.respectTransparency false in
      simp only [ne_eq, map_eq_bot_iff, M.property, not_false_eq_true, map_eq_top_iff, and_self]⟩
  left_inv M := by simp only [OrderIso.symm_apply_apply, Subtype.coe_eta]
  right_inv M := by simp only [ne_eq, OrderIso.apply_symm_apply, Subtype.coe_eta]
def Lattice.submoduleNeAndNeEquivLtAndLt (L : BruhatTits.Lattice R) :
    { M : { M : Submodule R L.M // maximalIdeal R • ⊤ ≤ M } // M ≠ ⊥ ∧ M ≠ ⊤ } ≃
      { M : Submodule R (Fin 2 → K) // maximalIdeal R • L.M < M ∧ M < L.M } where
  toFun M := ⟨Submodule.map L.M.subtype M.val.val, by
    refine ⟨ideal_smul_lt_of_ne_bot _ _ M.property.left, ?_⟩
    apply lt_of_ne_top
    exact M.property.right⟩
  invFun M := ⟨⟨Submodule.comap L.M.subtype M, by
      rw [← Submodule.comap_subtype_smul]
      apply Submodule.comap_mono
      exact le_of_lt M.property.left⟩, by
    refine ⟨?_, ?_⟩
    · simp only [ne_eq, Submodule.quotient_equiv_eq_bot_iff]
      intro hc
      apply_fun Submodule.map L.M.subtype at hc
      rw [Submodule.map_comap_eq_self, Submodule.map_subtype_smul] at hc
      absurd hc
      exact ne_of_gt M.property.left
      simp only [Submodule.range_subtype]
      exact le_of_lt M.property.right
    · simp only [ne_eq, le_top, Subtype.mk_eq_top_iff, Submodule.comap_subtype_eq_top]
      exact not_le_of_gt M.property.right⟩
  left_inv M := by
    ext : 2
    simp only [ne_eq, Submodule.comap_map_eq_self, Submodule.ker_subtype, bot_le]
  right_inv M := by
    ext : 1
    dsimp only
    rw [Submodule.map_comap_eq_self]
    simp only [Submodule.range_subtype]
    exact le_of_lt M.property.right
open Pointwise
def Lattice.standardNeighboursEquivLinesAux (L : BruhatTits.Lattice R) :
    { M : Submodule R (Fin 2 → K) // maximalIdeal R • L.M < M ∧ M < L.M } ≃
      { M : BruhatTits.Lattice R // IsStandardNeighbour M L } where
  toFun M := ⟨⟨M, .of_le_of_isLattice_right L.M M
      (le_of_lt M.property.right) (le_of_lt M.property.left)⟩,
    M.property.right, fun ϖ hϖ ↦ by
      rw [← maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact M.property.left⟩
  invFun M := ⟨M.val.M, by
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
      rw [maximalIdeal_smul_eq_uniformizer_smul _ hϖ]
      exact M.property.ϖlt ϖ hϖ, M.property.lt⟩
  left_inv M := rfl
  right_inv M := rfl
def standardNeighboursEquivLines (L : BruhatTits.Lattice R) :
    { M : BruhatTits.Lattice R // IsStandardNeighbour M L } ≃
      { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } :=
  L.standardNeighboursEquivLinesAux.symm.trans <|
    L.submoduleNeAndNeEquivLtAndLt.symm.trans (linesQuotientEquiv L).symm
def neighborsEquivLines (L : BruhatTits.Lattice R) :
    { y : Vertices R // IsNeighbour y ⟦L⟧ } ≃
      { M : Submodule (ResidueField R) L.quotient // Module.finrank (ResidueField R) M = 1 } :=
  (neighborsEquivStandardNeighbors L).trans (standardNeighboursEquivLines L)
open scoped LinearAlgebra.Projectivization
def neighborSetEquivProjectivization (L : BruhatTits.Lattice R) :
    BTgraph.neighborSet ⟦L⟧ ≃ ℙ (ResidueField R) L.quotient :=
  (Equiv.setCongr <| by ext; simp [BTgraph_adj, isNeighbour_symm]; rfl).trans <|
  (neighborsEquivLines L).trans
    (Projectivization.equivSubmodule (ResidueField R) L.quotient).symm
variable [Finite (ResidueField R)]
instance (x : Vertices R) : Finite ((BTgraph (R := R)).neighborSet x) := by
  refine Quotient.inductionOn x (fun L ↦ ?_)
  show Finite {y : Vertices R // IsNeighbour ⟦L⟧ y}
  have : Finite L.quotient := Module.finite_of_finite (ResidueField R)
  apply Finite.of_equiv _ (neighborSetEquivProjectivization L).symm
instance (x : Vertices R) : Fintype ((BTgraph (R := R)).neighborSet x) :=
  Fintype.ofFinite _
end BruhatTits


