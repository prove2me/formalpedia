-- Prove2me | Definitions.Def_BruhatTits_Lattice_Distance
-- name    : BruhatTits_Lattice_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T10:46:23.978746+00:00
-- url     : https://prove2.me/theorems/b6e63083-6c00-4412-b380-d763d3f94bfd
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Theorems.Thm_Basis_toGL_toSubmodule
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_smul_toSubmodule
import Theorems.Thm_P2M_cartan_decomposition__b636da006c62
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
namespace BruhatTits
omit [IsDiscreteValuationRing R] in
lemma smulBasis_apply_of_isLattice {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) (i j : ι) :
    ((smulBasis g b) i).val j = (b.toGL * g) j i := by
  dsimp only [smulBasis, toLinearEquivOfBasis]
  simp only [Basis.map_apply, LinearEquiv.trans_apply, Basis.equivFun_apply, Basis.repr_self,
    Basis.equivFun_symm_apply, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, «GL».map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
    coe_units_inv, Units.val_mul]
  change (Finset.univ.sum fun x ↦ g.val.mulVec (Finsupp.single i 1) x * (b x).val j) =
    (b.toGL * g.val.map Subtype.val) j i
  rw [Finsupp.single_eq_pi_single]
  simp only [mulVec_single, mul_one]
  rw [Matrix.mul_apply]
  congr
  ext k
  simp [Basis.toGL_apply, map_apply, mul_comm]
instance : MulAction.IsPretransitive (GL (Fin 2) K) (BruhatTits.Lattice R) where
  exists_smul_eq L M := by
    classical
    let bL : Basis (Fin 2) R L.M :=
      Module.finBasisOfFinrankEq R L.M (IsLattice.finrank L.M)
    let gL := bL.toGL
    have hL : gL.toSubmodule = L.M :=
      bL.toGL_toSubmodule
    let bM : Basis (Fin 2) R M.M :=
      Module.finBasisOfFinrankEq R M.M (IsLattice.finrank M.M)
    let gM := bM.toGL
    have hM : gM.toSubmodule = M.M :=
      bM.toGL_toSubmodule
    use gM * gL⁻¹
    apply BruhatTits.Lattice.ext
    rw [Lattice.smul_M, ← hM, ← hL, smul_toSubmodule]
    simp
omit [IsDiscreteValuationRing ↥R] in
lemma basis_smul_def_of_isLattice {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) (i j : ι) :
    (((MulOpposite.op g) • b) i).val j = (b.toGL * g) j i :=
  smulBasis_apply_of_isLattice g b i j
set_option synthInstance.maxHeartbeats 300000 in
omit [IsDiscreteValuationRing ↥R] in
@[simp]
lemma basis_smul_toGL {M : Submodule R (ι → K)} [IsLattice M] (g : GL ι R)
    (b : Basis ι R M) :
    ((MulOpposite.op g) • b).toGL = b.toGL * g := by
  ext i j
  simp [basis_smul_def_of_isLattice]
section
variable (ϖ : R) (hϖ : Irreducible ϖ)
include hϖ in
/--
Given two `R`-lattices `M` and `L`, there exists a basis `bM` of `M`
and a basis `bL` of `L` such that `bLᵢ = ϖ ^ fᵢ • bMᵢ` for `i = 1,2` and integers
`fᵢ`. If we fix the order of `fᵢ` to be `f₁ ≥ f₂`, the `fᵢ` are unique, i.e. don't
depend on `ϖ`, `bM` or `bL`.
-/
lemma exists_normal_basis (M L : BruhatTits.Lattice R) :
    ∃ (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
    Antitone f ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let bL : Basis (Fin 2) R L.M := L.basis
    let bM : Basis (Fin 2) R M.M := M.basis
    obtain ⟨(k₁ : GL (Fin 2) R), (k₂ : GL (Fin 2) R), f, hf, hk⟩ :=
      cartan_decomposition' (k := 2) ϖ hϖ (bM.toGL⁻¹ * bL.toGL)
    have hk := congrArg (fun g : GL (Fin 2) K => bM.toGL * g) hk
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at hk
    let bM' : Basis (Fin 2) R M.M :=
      (MulOpposite.op k₁) • bM
    let bL' : Basis (Fin 2) R L.M :=
      (MulOpposite.op k₂⁻¹) • bL
    use bM', bL', f, hf
    intro i
    simp only [bL', bM']
    ext j
    rw [basis_smul_def_of_isLattice, ← hk]
    simp only [PNat.val_ofNat, GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype,
      Units.inv_eq_val_inv, coe_units_inv, inv_inv, Units.val_mul, val_cartanDiag, Pi.smul_apply,
      smul_eq_mul]
    rw [basis_smul_def_of_isLattice]
    simp only [GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
      coe_units_inv, Units.val_mul]
    let mm : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K := (· * ·)
    change (mm (mm (mm (mm bM.toGL.val (k₁.val.map R.subtype))
      (cartanDiag ϖ hϖ f).val) (k₂.val.map R.subtype)) (((k₂.val)⁻¹).map R.subtype)) j i =
        (ϖ : K) ^ f i * (mm bM.toGL.val (k₁.val.map R.subtype)) j i
    dsimp only [mm]
    simp only [mul_assoc]
    erw [Subring.coe_map_mul_map_inv R k₂]
    simp only [mul_one, ← mul_assoc, val_cartanDiag, mul_diagonal]
    exact mul_comm _ _
end
lemma exists_normal_basis_uniformizer (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
    Irreducible ϖ ∧ Antitone f ∧ ∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨bM, bL, f, hf, heq⟩ := exists_normal_basis ϖ hϖ M L
  use ϖ, bM, bL, f
section Choices
noncomputable def signatureϖ (M L : BruhatTits.Lattice R) : R :=
  (exists_normal_basis_uniformizer M L).choose
noncomputable def signatureϖ_irreducible (M L : BruhatTits.Lattice R) :
    Irreducible (signatureϖ M L) :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose_spec.left
noncomputable def signatureBasisSource (M L : BruhatTits.Lattice R) :
    Basis (Fin 2) R M.M :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose
noncomputable def signatureBasisTarget (M L : BruhatTits.Lattice R) :
    Basis (Fin 2) R L.M :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose
noncomputable def signature (M L : BruhatTits.Lattice R) : Fin 2 → ℤ :=
  (exists_normal_basis_uniformizer M L).choose_spec.choose_spec.choose_spec.choose
end Choices
noncomputable def dist (M L : BruhatTits.Lattice R) : ℕ :=
  (signature M L 0 - signature M L 1).toNat
noncomputable def mulBasis (g : GL ι K) {M : Submodule R (ι → K)} (b : Basis ι R M) :
    Basis ι R (g • M : Submodule R (ι → K)) :=
  let e' : M ≃ₗ[R] (g • M : Submodule R (ι → K)) := equivSMulGL g M
  b.map e'
open Pointwise
def equivSMul (a : Kˣ) (M : Submodule R (ι → K)) :
    M ≃ₗ[R] (a • M : Submodule R (ι → K)) :=
  let e : (ι → K) ≃ₗ[R] (ι → K) := (LinearEquiv.smulOfUnit a).restrictScalars R
  e.submoduleMap M
noncomputable def mulBasisScalar (a : Kˣ) {M : BruhatTits.Lattice R} (b : Basis ι R M.M) :
    Basis ι R (a • M).M :=
  let e : M.M ≃ₗ[R] (a • M.M : Submodule R (Fin 2 → K)) := equivSMul a M.M
  b.map e
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
variable [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
end BruhatTits


