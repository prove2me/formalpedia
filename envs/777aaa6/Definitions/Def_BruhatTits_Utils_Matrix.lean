-- Prove2me | Definitions.Def_BruhatTits_Utils_Matrix
-- name    : BruhatTits_Utils_Matrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:48:05.183968+00:00
-- url     : https://prove2.me/theorems/6b419c14-bfe0-4d47-aca2-bea893cc89b4
-- title:
--   Matrix
-- statement:
--   Definitions and structural lemmas for Matrix, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
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
attribute [local simp] Subring.coe_det
attribute [local simp] Subring.coe_map_inv_mul_map
attribute [local simp] Subring.coe_map_mul_map_inv
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


set_option autoImplicit false
open BigOperators
namespace Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
section Coeffs
noncomputable def coeffs (g : Matrix n m R) : Set R :=
  Set.image2 g Set.univ Set.univ
lemma mem_coeffs (g : Matrix n m R) (i : n) (j : m) : g i j ∈ g.coeffs := by
  simp [coeffs]
lemma coeffs_nonempty [Nonempty n] [Nonempty m] (g : Matrix n m R) : g.coeffs.Nonempty :=
  have ⟨i⟩ := (inferInstance : Nonempty n)
  have ⟨j⟩ := (inferInstance : Nonempty m)
  ⟨g i j, g.mem_coeffs i j⟩
lemma finite_coeffs [Finite n] [Finite m] (g : Matrix n m R) :
    (coeffs g).Finite := by
  simp only [coeffs]
  exact Set.toFinite (Set.image2 g Set.univ Set.univ)
@[simp]
lemma transpose_coeffs (g : Matrix n m R) : g.transpose.coeffs = g.coeffs := by
  ext a
  simp only [coeffs, Finset.mem_image₂, Finset.mem_univ, transpose_apply, true_and]
  constructor
  · rintro ⟨i, -, j, -, hij⟩
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use j, i
  · rintro ⟨i, -, j, -, hij⟩
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use j, i
@[simp]
lemma coeffs_reindex (g : Matrix n m R) (e : n ≃ n') (f : m ≃ m') :
    (reindex e f g).coeffs = g.coeffs := by
  ext a
  simp only [coeffs, reindex_apply, submatrix_apply, Set.mem_image2, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, j, hij⟩
    use e.symm i, f.symm j
  · intro ⟨i, j, hij⟩
    use e i, f j
    simpa
@[simp]
lemma coeffs_one [One R] [Zero R] [DecidableEq n] : (1 : Matrix n n R).coeffs ⊆ {0, 1} := by
  intro a
  simp only [coeffs, Set.mem_image2, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_exists_index]
  intro i j hij
  by_cases h : i = j
  · subst h
    simpa [one_apply_eq] using Or.inr hij.symm
  · simpa [one_apply_ne h] using Or.inl hij.symm
end Coeffs
section Map
variable [CommRing R] [DecidableEq m] [DecidableEq n] [Fintype n] [Fintype m]
variable {S : Type*} [CommRing S] {F : Type*} (f : R →+* S)
@[simp]
lemma map_ite (p : Prop) (a b : R) [Decidable p] : f (if p then a else b) = if p then f a else f b := by
  split_ifs <;> rfl
omit [Fintype n] in
@[simp]
lemma map_transvection (i j : n) (c : R) : (transvection i j c).map f = transvection i j (f c) := by
  simp only [transvection]
  ext a b
  simp only [map_apply, add_apply, single, map_add, map_ite, map_zero, add_left_inj]
  by_cases h : a = b
  . subst h
    simp
  · simp_all
end Map
variable [CommRing R]
section CoeffsSup
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
section Finite
variable [Finite n] [Finite m] [Finite n'] [Finite m'] [Nonempty n] [Nonempty m]
  [Nonempty n'] [Nonempty m']
noncomputable def coeffs_sup (g : Matrix n m R) : Γ₀ :=
  Finset.sup' (finite_coeffs g).toFinset (by simpa using coeffs_nonempty g) v
lemma coeff_le_coeffs_sup (g : Matrix n m R)
    (i : n) (j : m) : v (g i j) ≤ g.coeffs_sup v :=
  Finset.le_sup' _ (by simpa using mem_coeffs g i j)
lemma coeffs_sup_exists_repr (g : Matrix n m R) :
    ∃ p : n × m, v (g p.1 p.2) = g.coeffs_sup v := by
  simp only [coeffs_sup]
  by_contra h
  simp only [Prod.exists, not_exists] at h
  have : g.coeffs_sup v < g.coeffs_sup v := by
    simp only [coeffs_sup, Finset.sup'_lt_iff]
    intro a ha
    simp only [coeffs, Set.Finite.mem_toFinset, Set.mem_image2, Set.mem_univ, true_and] at ha
    obtain ⟨i, j, rfl⟩ := ha
    exact lt_of_le_of_ne (coeff_le_coeffs_sup v g i j) (h i j)
  simp_all
noncomputable def coeffs_sup_at (g : Matrix n m R) : n × m :=
  (g.coeffs_sup_exists_repr v).choose
end Finite
section Fintype
variable [DecidableEq m] [Fintype n] [Fintype m]
@[simp]
lemma mul_swap_coeffs (g : Matrix m m R) (i j : m) :
    (g * swap R i j).coeffs = g.coeffs := by
  ext a
  simp only [coeffs, Finset.mem_image₂, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, -, k, -, hlk⟩
    by_cases hjl : k = j
    subst hjl
    simp only [mul_swap_apply_right] at hlk
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use l, i
    by_cases hik : k = i
    subst hik
    simp only [mul_swap_apply_left] at hlk
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use l, j
    rw [mul_swap_of_ne hik hjl] at hlk
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use l, k
  · rintro ⟨l, -, k, -, hlk⟩
    by_cases hjl : k = j
    · subst hjl
      simp only [Set.mem_image2, Set.mem_univ, true_and]
      use l, i
      simpa
    · simp only [Set.mem_image2, Set.mem_univ, true_and]
      by_cases hik : k = i
      · subst hik
        use l, j
        simpa
      · use l, k
        simpa only [mul_swap_of_ne hik hjl]
@[simp]
lemma swap_mul_coeffs (g : Matrix m m R) (i j : m) :
    (swap R i j * g).coeffs = g.coeffs := by
  classical
  rw [← transpose_coeffs]
  simp only [transpose_mul, transpose_swap, mul_swap_coeffs, transpose_coeffs]
omit [Fintype n] in
@[simp]
lemma coeffs_sup_mul_swap [Nonempty m] (g : Matrix m m R) (i j : m) :
    (g * swap R i j).coeffs_sup v = g.coeffs_sup v := by
  simp only [coeffs_sup, mul_swap_coeffs]
@[simp]
lemma coeffs_sup_swap_mul [Nonempty m] (g : Matrix m m R) (i j : m) :
    (swap R i j * g).coeffs_sup v = g.coeffs_sup v := by
  simp only [coeffs_sup, swap_mul_coeffs]
variable [Fintype n'] [Nonempty n'] [Fintype m'] [Nonempty m']
variable [DecidableEq n'] [DecidableEq m']
variable [Nonempty n] [Nonempty m]
end Fintype
end CoeffsSup
section GeneralLinearGroup
variable [DecidableEq n] [Fintype n]
def TransvectionStruct.toGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := t.mul_inv
  inv_val := t.inv_mul
@[simps]
def GL.transpose (g : GL n R) : GL n R where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by
    rw [← Matrix.transpose_mul]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul]
    simp
@[simps]
def GL.diagonal (g : n → Rˣ) : GL n R where
  val := Matrix.diagonal (fun j ↦ g j)
  inv := Matrix.diagonal (fun j ↦ (g j).inv)
  val_inv := by simp
  inv_val := by simp
variable [DecidableEq m] [Fintype m]
@[simps]
def GL.diagonalBlocks (g : GL n R) (h : GL m R) : GL (n ⊕ m) R where
  val := Matrix.fromBlocks g 0 0 h
  inv := Matrix.fromBlocks g.inv 0 0 h.inv
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp
@[simps]
def GL.reindex (e : n ≃ m) (g : GL n R) : GL m R where
  val := Matrix.reindex e e g
  inv := Matrix.reindex e e g.inv
  val_inv := by simp
  inv_val := by simp
namespace GeneralLinearGroup
lemma coe_inv_mul (g : GL n R) : g.val⁻¹ * g.val = 1 := by
  simp
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}
section Basis
noncomputable def toBasis (g : GL ι K) : Basis ι K (ι → K) :=
  Basis.ofEquivFun (toLin g⁻¹).toLinearEquiv
@[simp]
lemma toBasis_coe_apply (g : GL ι K) (i : ι) : g.toBasis i = (fun j ↦ g j i) := by
  simp only [toBasis, map_inv, Basis.coe_ofEquivFun]
  show (toLin g⁻¹).toLinearEquiv.symm (Pi.single i 1) = fun j ↦ g j i
  have h : Pi.single i 1 = g.inv *ᵥ (fun j ↦ g j i) := by
    simp only [Units.inv_eq_val_inv, coe_units_inv]
    rw [show (fun j ↦ g j i) = g.val *ᵥ Pi.single i 1 from by ext; simp]
    have : Nonempty ι := ⟨ i ⟩
    rw [mulVec_mulVec, coe_inv_mul]
    rw [one_mulVec]
  rw [h]
  erw [← toLin_apply g]
  rw [toLin_apply g, ← h]
  ext
  simp
def toSubmodule (g : GL ι K) : Submodule R (ι → K) :=
  Submodule.span R (Set.range (fun col row ↦ g.val row col))
end Basis
instance : SMul (GL ι K) (Submodule R (ι → K)) where
  smul g M := Submodule.map ((toLin g).val : (ι → K) →ₗ[R] ι → K) M
lemma smul_def (g : GL ι K) (M : Submodule R (ι → K)) :
    g • M = Submodule.map (g.val.mulVecLin : (ι → K) →ₗ[R] ι → K) M :=
  rfl
instance : MulAction (GL ι K) (Submodule R (ι → K)) where
  one_smul M := by
    rw [smul_def]
    ext
    simp
  mul_smul g h M := by
    simp_rw [smul_def]
    ext
    simp
def equivSMulGL (g : GL ι K) (M : Submodule R (ι → K)) :
    M ≃ₗ[R] (g • M : Submodule R (ι → K)) :=
  ((toLin g).toLinearEquiv.restrictScalars R).submoduleMap M
noncomputable def toLinearEquivOfBasis {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (b : Basis ι R M) (g : GL ι R) : M ≃ₗ[R] M :=
  let f : (ι → R) ≃ₗ[R] ι → R := (toLin g).toLinearEquiv
  b.equivFun ≪≫ₗ f ≪≫ₗ b.equivFun.symm
noncomputable def smulBasis {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] (g : GL ι R)
    (b : Basis ι R M) : Basis ι R M :=
  b.map (toLinearEquivOfBasis b g)
noncomputable instance (M : Submodule R (ι → K)) : SMul (GL ι R)ᵐᵒᵖ (Basis ι R M) where
  smul := fun ⟨g⟩ b ↦ smulBasis g b
lemma basis_smul_def {M : Submodule R (ι → K)} (g : GL ι R) (b : Basis ι R M) :
    (MulOpposite.op g) • b = smulBasis g b :=
  rfl
@[simp]
lemma ofLinearEquiv_toLinearEquiv {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (f : M ≃ₗ[R] M) : (LinearMap.GeneralLinearGroup.ofLinearEquiv f).toLinearEquiv = f :=
  rfl
instance (M : Submodule R (ι → K)) :
    MulAction.IsPretransitive (GL ι R)ᵐᵒᵖ (Basis ι R M) where
  exists_smul_eq b b' := by
    let e : M ≃ₗ[R] M := Module.Basis.equiv b b' (Equiv.refl ι)
    let e' : (ι → R) ≃ₗ[R] ι → R :=
      b.equivFun.symm ≪≫ₗ e ≪≫ₗ b.equivFun
    let g : GL ι R := toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e')
    use ⟨g⟩
    erw [basis_smul_def]
    simp only [smulBasis, g, e', e,
      toLinearEquivOfBasis, MulEquiv.apply_symm_apply, ofLinearEquiv_toLinearEquiv]
    show b.map (b.equivFun ≪≫ₗ b.equivFun.symm ≪≫ₗ Module.Basis.equiv b b' (Equiv.refl ι) ≪≫ₗ (b.equivFun ≪≫ₗ
      b.equivFun.symm)) = b'
    simp
@[simps]
def embDiagonal (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    Rˣ →* GL ι R where
  toFun x := Matrix.GL.diagonal (fun _ ↦ x)
  map_one' := by ext; simp
  map_mul' x y := by
    ext i j
    by_cases h : i = j <;> simp [h]
end GeneralLinearGroup
end GeneralLinearGroup
section UpperTriangular
def GeneralLinearGroup.upperTriangularSubgroup (R : Type*) [CommRing R]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    Subgroup (GL ι R) where
  carrier := { g | g.val.BlockTriangular id }
  mul_mem' {x y} hx hy := hx.mul hy
  one_mem' := Matrix.blockTriangular_one
  inv_mem' {x} hx := by
    letI : Invertible x.val := ⟨x.inv, x.4, x.3⟩
    convert Matrix.blockTriangular_inv_of_blockTriangular hx
    simp
end UpperTriangular
end Matrix


