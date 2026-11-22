-- Prove2me | solution 1 for Matrix.GL.conj_diagonal_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:49:22.19247+00:00
-- url     : https://prove2.me/submissions/a0008d25-ad29-4957-aadd-bf245a15debd

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
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
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
namespace Matrix
namespace «GL»
theorem _root_.solution {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → Rˣ) (g : GL ι R) (i j : ι) :
    MulAut.conj (Matrix.GL.diagonal d) g i j = (d i) * (d j)⁻¹ * g i j := by
  have heq : Ring.inverse (fun j ↦ (d j).val) = fun j ↦ (d j).inv := by
    let u : (ι → R)ˣ := .mkOfMulEqOne (fun j ↦ d j) (fun j ↦ (d j).inv) ?_
    · exact Ring.inverse_unit u
    · ext; simp
  simp only [MulAut.conj_apply, Units.val_mul, Matrix.GL.val_diagonal, Matrix.coe_units_inv]
  rw [Matrix.inv_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, heq]
  field_simp
  change (d i : R) * g i j * (d j).inv = (d i : R) * (d j).inv * g i j
  ring
end «GL»
end Matrix
