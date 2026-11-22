-- Prove2me | solution 1 for P2M_exists_normalization0__0f257ed9185d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:19:31.653768+00:00
-- url     : https://prove2.me/submissions/97705934-bb9e-4103-af12-d8d72e3b3c60

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Mathlib
import Definitions.Def_BruhatTits_Cartan_Existence
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Matrix_coeffs_sup_at_sup
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
variable {K : Type*} [Field K]
variable {R : Subring K} [ValuationRing R] [IsFractionRing R K]
local notation "v" => ValuationRing.valuation R K
attribute [-simp] Subring.coe_subtype
theorem _root_.solution {k : ℕ+} (g : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) K) :
    ∃ (k₁ k₂ : GL (Fin k ⊕ Unit) R),
    v ((k₁.val * g * k₂.val) (Sum.inr ()) (Sum.inr ())) = (k₁.val * g * k₂.val).coeffs_sup v
    ∧ (k₁.val * g * k₂.val).coeffs_sup v = g.coeffs_sup v := by
  -- the maximal element is in row `p.1` and column `p.2`
  let p := g.coeffs_sup_at v
  -- swap `i`-th row with last row and `j`-th col with last col
  let k₁ := Matrix.GeneralLinearGroup.swap R (Sum.inr ()) p.1
  let k₂ := Matrix.GeneralLinearGroup.swap R (Sum.inr ()) p.2
  have hv : v ((k₁.val * g * k₂.val) (Sum.inr ()) (Sum.inr ())) =
      (k₁.val * g * k₂.val).coeffs_sup v := by
    simp only [Matrix.GeneralLinearGroup.val_swap, Matrix.map_swap, Matrix.mul_swap_apply_left,
      Matrix.swap_mul_apply_left, Matrix.coeffs_sup_mul_swap, Matrix.coeffs_sup_swap_mul, k₁, p, k₂]
    rw [← Matrix.coeffs_sup_at_sup]
  refine ⟨.swap R (Sum.inr ()) p.1, .swap R (Sum.inr ()) p.2, hv, ?_⟩
  · rw [← hv]
    simp only [Matrix.GeneralLinearGroup.val_swap, Matrix.map_swap, Matrix.mul_swap_apply_left,
      Matrix.swap_mul_apply_left, k₁, p, k₂]
    rw [← Matrix.coeffs_sup_at_sup]
