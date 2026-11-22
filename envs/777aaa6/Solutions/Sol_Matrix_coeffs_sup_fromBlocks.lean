-- Prove2me | solution 1 for Matrix.coeffs_sup_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:53:38.563287+00:00
-- url     : https://prove2.me/submissions/a8f58a5f-0cae-49cc-8e63-2e79e0d5ce80

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
import Theorems.Thm_Matrix_coeffs_fromBlocks
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
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
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [Finite n] [Finite m] [Finite n'] [Finite m'] [Nonempty n] [Nonempty m]
  [Nonempty n'] [Nonempty m']
namespace Matrix
theorem _root_.solution (A : Matrix n n' R) (B : Matrix n m R)
    (C : Matrix m' n' R) (D : Matrix m' m R) :
    (A.fromBlocks B C D).coeffs_sup v =
      A.coeffs_sup v ⊔ B.coeffs_sup v ⊔ C.coeffs_sup v ⊔ D.coeffs_sup v := by
  classical
  simp only [coeffs_sup, ← Finset.sup'_union, coeffs_fromBlocks]
  congr
  ext
  simp
  tauto
end Matrix
