-- Prove2me | Definitions.Def_BruhatTits_Lattice_Construction
-- name    : BruhatTits_Lattice_Construction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:09:19.157496+00:00
-- url     : https://prove2.me/theorems/7f55c3e3-d3d6-4bf0-b934-59ef949ac475
-- title:
--   Construction
-- statement:
--   Definitions and structural lemmas for Construction, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Construction.lean

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Theorems.Thm_Basis_linearIndependent_of_submodule
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
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
namespace Basis
variable {ι : Type*}
def toSubmodule (b : Basis ι K (ι → K)) : Submodule R (ι → K) :=
  Submodule.span R (Set.range b)
lemma self_mem_toSubmodule (b : Basis ι K (ι → K)) (i : ι) : b i ∈ b.toSubmodule (R := R) := by
  simp [toSubmodule]
  apply Submodule.subset_span
  use i
open Classical in
lemma toSubmodule_isLattice [Fintype ι] (b : Basis ι K (ι → K)) : IsLattice (R := R) b.toSubmodule where
  isFG := ⟨Finset.image b Finset.univ, by simp [toSubmodule]⟩
  spans := by
    rw [_root_.eq_top_iff]
    rw [← b.span_eq]
    apply Submodule.span_mono
    simp only [toSubmodule]
    intro x hx
    simp only [SetLike.mem_coe]
    apply Submodule.subset_span
    exact hx
def toLattice (b : Basis (Fin 2) K (Fin 2 → K)) : BruhatTits.Lattice R where
  M := b.toSubmodule
  isLattice := b.toSubmodule_isLattice
@[simp]
lemma toLattice_module (b : Basis (Fin 2) K (Fin 2 → K)) :
    (b.toLattice (R := R)).M = b.toSubmodule :=
  rfl
def twist' [Fintype ι] (b : Basis ι K (ι → K)) (f : ι → Kˣ) : Basis ι K (ι → K) :=
  let v (i : ι) : (ι → K) := (f i).val • b i
  have hli : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro s g hg
    simp only [v, smul_smul] at hg
    intro i hi
    have := linearIndependent_iff'.mp b.linearIndependent s _ hg i hi
    refine eq_zero_of_ne_zero_of_mul_right_eq_zero ?_ this
    exact (f i).ne_zero
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hli.span_eq_top_of_card_eq_finrank']
    exact (Module.finrank_fintype_fun_eq_card K).symm
  Basis.mk hli hsp
@[simp]
lemma twist'_apply [Fintype ι] (b : Basis ι K (ι → K)) (f : ι → Kˣ) (i : ι) :
    b.twist' f i = f i • b i := by
  simp [twist', Units.smul_def]
def twist [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) :
    Basis ι K (ι → K) :=
  have hϖ' : ϖ.val ≠ 0 := by simpa using hϖ.ne_zero
  b.twist' (fun i ↦ Units.mk0 ϖ.val hϖ' ^ f i)
@[simp]
lemma twist_apply [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℤ) (i : ι) :
    b.twist hϖ f i = ϖ.val ^ f i • b i := by
  simp [twist, Units.smul_def]
def ntwist [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℕ) :
    Basis ι K (ι → K) :=
  b.twist hϖ (fun i ↦ f i)
@[simp]
lemma ntwist_apply [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f : ι → ℕ) (i : ι) :
    b.ntwist hϖ f i = ϖ ^ f i • b i := by
  simp [ntwist, Subring.smul_def]
def twist₂ (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℤ) :
    Basis (Fin 2) K (Fin 2 → K) :=
  b.twist hϖ (fun i ↦ match i with
    | 0 => n
    | 1 => m)
@[simp]
lemma twist₂_apply₀ (b : Basis (Fin 2) K ((Fin 2) → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℤ) :
    b.twist₂ hϖ n m 0 = ϖ.val ^ n • b 0 := by
  simp [twist₂]
@[simp]
lemma twist₂_apply₁ (b : Basis (Fin 2) K ((Fin 2) → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℤ) :
    b.twist₂ hϖ n m 1 = ϖ.val ^ m • b 1 := by
  simp [twist₂]
def ntwist₂ (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℕ) :
    Basis (Fin 2) K (Fin 2 → K) :=
  b.twist₂ hϖ n m
@[simp]
lemma ntwist₂_apply₀ (b : Basis (Fin 2) K ((Fin 2) → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℕ) :
    b.ntwist₂ hϖ n m 0 = ϖ ^ n • b 0 := by
  simp [ntwist₂, Subring.smul_def]
@[simp]
lemma ntwist₂_apply₁ (b : Basis (Fin 2) K ((Fin 2) → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℕ) :
    b.ntwist₂ hϖ n m 1 = ϖ ^ m • b 1 := by
  simp [ntwist₂, Subring.smul_def]
section LE
open BigOperators
end LE
section fromLattice
variable [IsFractionRing R K] [Fintype ι]
def fromSubmoduleOfIsLattice {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    Basis ι K (ι → K) :=
  have hli : LinearIndependent K (fun i ↦ (b i).val) :=
    b.linearIndependent_of_submodule
  have hsp : ⊤ ≤ Submodule.span K (Set.range <| fun i ↦ (b i).val) :=
    b.top_le_submodule_span_of_isLattice
  Basis.mk hli hsp
@[simp]
lemma fromSubmoduleOfIsLattice_apply {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M)
    (i : ι) : b.fromSubmoduleOfIsLattice i = b i := by
  simp [fromSubmoduleOfIsLattice]
def fromLattice {M : BruhatTits.Lattice R} (b : Basis (Fin 2) R M.M) :
    Basis (Fin 2) K (Fin 2 → K) :=
  fromSubmoduleOfIsLattice b
@[simp]
lemma fromLattice_apply {M : BruhatTits.Lattice R} (b : Basis (Fin 2) R M.M) (i : Fin 2) :
    b.fromLattice i = b i := by
  simp [fromLattice]
@[simp]
lemma toSubmodule_fromLattice {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    b.fromSubmoduleOfIsLattice.toSubmodule = M := by
  simp only [toSubmodule]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro - ⟨i, rfl⟩
    simp
  · simp_rw [← Submodule.map_subtype_top M, ← b.span_eq]
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro - ⟨i, ⟨a, rfl⟩, rfl⟩
    simp
@[simp]
lemma toLattice_fromLattice {M : BruhatTits.Lattice R} (b : Basis (Fin 2) R M.M) :
    b.fromLattice.toLattice = M := by
  apply BruhatTits.Lattice.ext
  simp [fromLattice]
end fromLattice
section Restrict
variable [IsFractionRing R K] [Fintype ι]
def restrict (b : Basis ι K (ι → K)) : Basis ι R (b.toSubmodule (R := R)) :=
  let v (i : ι) : (b.toSubmodule (R := R)) := ⟨b i, b.self_mem_toSubmodule i⟩
  have hli : LinearIndependent R v := by
    apply LinearIndependent.of_comp (b.toSubmodule (R := R)).subtype
    rw [LinearIndependent.iff_fractionRing (R := R) (K := K)]
    exact b.linearIndependent
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    rintro ⟨x, hx⟩ -
    simp only [toSubmodule] at hx
    simp only [v]
    rw [Submodule.mem_span_range_iff_exists_fun] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    use c
    apply Subtype.ext
    simpa
  Basis.mk hli hsp
def restrictToLattice (b : Basis (Fin 2) K (Fin 2 → K)) :
    Basis (Fin 2) R (b.toLattice (R := R)).M :=
  b.restrict (R := R)
end Restrict
section GLSMul
variable [DecidableEq ι] [Fintype ι]
def smulGL (g : GL ι K) (b : Basis ι K (ι → K)) : Basis ι K (ι → K) :=
  b.map (g.toLin.toLinearEquiv)
instance : SMul (GL ι K) (Basis ι K (ι → K)) where
  smul g b := smulGL g b
end GLSMul
section SMul
variable [Fintype ι]
def smul' (a : Kˣ) (b : Basis ι K (ι → K)) : Basis ι K (ι → K) := b.twist' (fun _ ↦ a)
instance : SMul Kˣ (Basis ι K (ι → K)) where
  smul := smul'
open Pointwise
end SMul
section Swap
variable [Fintype ι] [DecidableEq ι]
def permMatrix (b : Basis ι K (ι → K)) (e : ι ≃ ι) : GL ι K :=
  Matrix.GeneralLinearGroup.toLin.symm <| .ofLinearEquiv <| Module.Basis.equiv b (b.reindex e) (Equiv.refl _)
def swap₂ : Fin 2 ≃ Fin 2 where
  toFun
    | 0 => 1
    | 1 => 2
  invFun
    | 0 => 1
    | 1 => 2
  left_inv := by decide
  right_inv := by decide
def swap (b : Basis (Fin 2) K (Fin 2 → K)) : Basis (Fin 2) K (Fin 2 → K) :=
  b.reindex swap₂
def swapMatrix (b : Basis (Fin 2) K (Fin 2 → K)) : GL (Fin 2) K :=
  b.permMatrix swap₂
end Swap
variable [IsFractionRing R K]
instance (b : Basis (Fin 2) K (Fin 2 → K)) :
    SMul R (b.toSubmodule (R := R)) :=
  b.toSubmodule.smul
end Basis
variable (R) in
/-- The standard `R`-lattice `R ⊕ R`. -/
def Lattice.standard : BruhatTits.Lattice R :=
  Basis.toLattice (Pi.basisFun K (Fin 2))
section
end


