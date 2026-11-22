-- Prove2me | solution 1 for Matrix.coeffs_sup_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:45.098499+00:00
-- url     : https://prove2.me/submissions/5dfe1b71-3179-44a8-b97a-246d45e763ea

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
import Theorems.Thm_Matrix_one_mem_coeffs_one
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
variable [DecidableEq m] [Fintype n] [Fintype m]
variable [Fintype n'] [Nonempty n'] [Fintype m'] [Nonempty m']
variable [DecidableEq n'] [DecidableEq m']
variable [Nonempty n] [Nonempty m]
namespace Matrix
theorem _root_.solution [DecidableEq n] : (1 : Matrix n n R).coeffs_sup v = 1 := by
  simp only [coeffs_sup]
  apply le_antisymm
  · simp only [Finset.sup'_le_iff]
    intro b hb
    simp only [Set.Finite.mem_toFinset] at hb
    apply coeffs_one at hb
    aesop
  · simp only [Finset.le_sup'_iff]
    use 1
    simpa using one_mem_coeffs_one
end Matrix
