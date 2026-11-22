-- Prove2me | Definitions.Def_BruhatTits_Lattice_Basic
-- name    : BruhatTits_Lattice_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:55:35.012661+00:00
-- url     : https://prove2.me/theorems/07e4fc66-7ffb-4365-98a4-5927b7770b20
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Basic.lean

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Theorems.Thm_Basis_linearIndependent_of_submodule
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_toSubmodule
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Pi_basisFun_eq_single
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
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


set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
class IsLattice (M : Submodule R (ι → K)) : Prop where
  /-- `M` is finitely generated. -/
  isFG : M.FG
  /-- `M` spans `ι → K` -/
  spans : Submodule.span K (M : Set (ι → K)) = ⊤
namespace IsLattice
variable (M : Submodule R (ι → K)) [IsLattice M]
instance finite : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact isFG
instance smul (a : Kˣ) : IsLattice (a • M) where
  isFG := by
    obtain ⟨s, hs⟩ := IsLattice.isFG (M := M)
    subst hs
    change ((a : K) • Submodule.span R (s : Set (ι → K))).FG
    rw [Submodule.smul_span]
    exact Submodule.fg_span ((Finset.finite_toSet s).image (fun v => (a : K) • v))
  spans := by
    change Submodule.span K (((a : K) • M) : Set (ι → K)) = ⊤
    rw [← Submodule.smul_span, IsLattice.spans]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    apply Submodule.smul_mem_pointwise_smul
    trivial
end IsLattice
variable [IsFractionRing R K]
namespace Matrix.GeneralLinearGroup
variable [Fintype ι] [DecidableEq ι]
instance toSubmodule_isLattice (g : GL ι K) :
    IsLattice (R := R) g.toSubmodule where
  isFG := Submodule.fg_def.mpr ⟨Set.range (fun col row ↦ g.val row col), Set.finite_range _, rfl⟩
  spans := by
    rw [_root_.eq_top_iff]
    let b := g.toBasis
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    erw [mem_toSubmodule]
    use Pi.single i 1
    ext
    simp [b]
instance (g : GL ι K) (M : Submodule R (ι → K)) [IsLattice M] : IsLattice (g • M) where
  isFG := by
    rw [GeneralLinearGroup.smul_def]
    apply Submodule.FG.map
    exact IsLattice.isFG
  spans := by
    rw [GeneralLinearGroup.smul_def]
    simp_rw [Submodule.map_coe, LinearMap.coe_restrictScalars, mulVecLin_apply]
    erw [Submodule.span_image g.val.mulVecLin]
    rw [IsLattice.spans]
    simp only [Submodule.map_top]
    rw [_root_.eq_top_iff]
    intro x _
    simp only [LinearMap.mem_range, mulVecLin_apply]
    use g⁻¹ *ᵥ x
    simp [mulVec_mulVec]
end Matrix.GeneralLinearGroup
namespace Basis
omit [IsFractionRing (↥R) K] in
lemma top_le_submodule_span_of_isLattice {κ : Type*} [Fintype κ]
    {M : Submodule R (ι → K)} (b : Basis κ R M)
    [IsLattice M] : ⊤ ≤ Submodule.span K (Set.range fun i ↦ (b i).val) := by
  rintro x -
  have hx : x ∈ Submodule.span K (M : Set (ι → K)) := by
    rw [IsLattice.spans]
    trivial
  induction' hx using Submodule.span_induction with x hx x y _ _ hx hy a x _ hx
  · have hv : ⟨x, hx⟩ ∈ Submodule.span R (Set.range b) := Basis.mem_span b ⟨x, hx⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, hc⟩ := hv
    apply congrArg Subtype.val at hc
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at hc
    rw [← hc]
    apply Submodule.sum_smul_mem
    intro i _
    apply Submodule.subset_span
    exact Set.mem_range_self i
  · simp
  · exact Submodule.add_mem _ hx hy
  · exact Submodule.smul_mem _ _ hx
variable [Fintype ι] [DecidableEq ι]
noncomputable def ofSubmodule {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    Basis ι K (ι → K) := Basis.mk (v := fun i : ι ↦ (b i).val)
  b.linearIndependent_of_submodule
  b.top_le_submodule_span_of_isLattice
noncomputable def toGeneralLinearGroup (b : Basis ι K (ι → K)) : GL ι K :=
  Matrix.GeneralLinearGroup.toLin.symm <| LinearMap.GeneralLinearGroup.ofLinearEquiv <|
    Basis.equiv (Pi.basisFun K ι) b (Equiv.refl ι)
@[simp]
lemma toGeneralLinearGroup_apply (b : Basis ι K (ι → K))
    (i j : ι) : b.toGeneralLinearGroup i j = b j i := by
  simp only [toGeneralLinearGroup, ofSubmodule,
    Matrix.GeneralLinearGroup.toLinear_symm_ofLinearEquiv_apply]
  rw [← Pi.basisFun_eq_single, Basis.equiv_apply]
  simp
noncomputable def toGL {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    GL ι K :=
  b.ofSubmodule.toGeneralLinearGroup
@[simp]
lemma toGL_apply {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M)
    (i j : ι) : b.toGL i j = (b j).val i := by
  simp [toGL, ofSubmodule]
@[simp]
lemma transpose_toGL {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M)
    (i : ι) : b.toGL.val.transpose i = b i := by
  ext
  simp
end Basis
section
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
instance IsLattice.free (M : Submodule R (ι → K)) [IsLattice M] : Module.Free R M :=
  by
    haveI : NoZeroSMulDivisors R M := ⟨by
      intro c x h
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        apply Subtype.ext
        funext i
        have hi := congrArg (fun z : M => (z : ι → K) i) h
        change (c : K) * (x : ι → K) i = 0 at hi
        have hc' : (c : K) ≠ 0 := fun h => hc (Subtype.ext h)
        exact (mul_eq_zero.mp hi).resolve_left hc'⟩
    exact Module.free_of_finite_type_torsion_free'
variable [Fintype ι]
theorem IsLattice.rank' (M : Submodule R (ι → K)) [IsLattice M] :
    Module.rank R M = Fintype.card ι := by
  --have : Module.Free R M := IsLattice.free M
  let b := Module.Free.chooseBasis R M
  have hli : LinearIndependent K (fun i ↦ (b i).val) :=
    Basis.linearIndependent_of_submodule b
  have hsp : ⊤ ≤ Submodule.span K (Set.range <| fun i ↦ (b i).val) :=
    Basis.top_le_submodule_span_of_isLattice b
  let b' := Basis.mk hli hsp
  rw [rank_eq_card_basis b, ← rank_eq_card_basis b', rank_fun']
theorem IsLattice.rank {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice M] : Module.rank R M = k := by
  rw [IsLattice.rank' M]
  simp
theorem IsLattice.finrank {k : ℕ} (M : Submodule R (Fin k → K)) [IsLattice M] :
    Module.finrank R M = k :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank M)
instance IsLattice.sup (M N : Submodule R (ι → K)) [IsLattice M] [IsLattice N] :
    IsLattice (M ⊔ N) where
  isFG := Submodule.FG.sup IsLattice.isFG IsLattice.isFG
  spans := by
    rw [_root_.eq_top_iff]
    trans
    · show ⊤ ≤ Submodule.span K M
      rw [IsLattice.spans (M := M)]
    · apply Submodule.span_mono
      simp
end
namespace BruhatTits
variable (R)
@[ext]
structure Lattice where
  M : Submodule R (Fin 2 → K)
  isLattice : IsLattice M := by infer_instance
namespace Lattice
attribute [instance] isLattice
instance : SMul Kˣ (Lattice R) where
  smul a L := { M := a • L.M }
omit [IsFractionRing R K] in
@[simp]
lemma smul_module (a : Kˣ) (L : Lattice R) : (a • L).M = a • L.M :=
  rfl
instance : MulAction Kˣ (Lattice R) where
  one_smul L := by
    apply Lattice.ext
    simp only [smul_module, one_smul]
  mul_smul a b L := by
    apply Lattice.ext
    simp only [smul_module, mul_smul]
instance : SMul (GL (Fin 2) K) (BruhatTits.Lattice R) where
  smul g L := { M := g • L.M }
variable {R}
omit [IsFractionRing R K] in
lemma smul_M (g : GL (Fin 2) K) (L : BruhatTits.Lattice R) :
    (g • L).M = g • L.M :=
  rfl
instance : MulAction (GL (Fin 2) K) (BruhatTits.Lattice R) where
  one_smul L := by
    apply BruhatTits.Lattice.ext
    rw [smul_M, one_smul]
  mul_smul g h L := by
    apply BruhatTits.Lattice.ext
    rw [smul_M]
    exact mul_smul g h L.M
variable [IsPrincipalIdealRing R]
noncomputable def basis (L : BruhatTits.Lattice R) :
    Basis (Fin 2) R L.M :=
  Module.finBasisOfFinrankEq R L.M (IsLattice.finrank L.M)
variable (R)
def IsSimilar (L N : Lattice R) : Prop := ∃ (a : Kˣ), a • L = N
omit [IsFractionRing R K] [IsPrincipalIdealRing R]
lemma IsSimilar.equivalence : Equivalence (IsSimilar R) where
  refl M := ⟨1, MulAction.one_smul M⟩
  symm {M N} h := by
    obtain ⟨a, ha⟩ := h
    use a⁻¹
    rw [← ha, inv_smul_smul]
  trans {M N P} h1 h2 := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    use b * a
    rw [← hb, ← ha, mul_smul]
instance IsSimilar.setoid : Setoid (Lattice R) where
  r := IsSimilar R
  iseqv := IsSimilar.equivalence R
end Lattice
end BruhatTits


