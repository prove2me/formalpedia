-- Prove2me | solution 1 for P2M_cartan_decomposition_unique__aux_3e99e4a3d7c4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:21:27.014609+00:00
-- url     : https://prove2.me/submissions/62cae3e8-8ebc-4a3f-9556-f7c74d3f3ce6

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Theorems.Thm_Finset_prod_zpow_eq_zpow_sum
import Theorems.Thm_GL_coe_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_one
import Theorems.Thm_IsLocalRing_exists_isUnit_of_isUnit_sum
import Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
import Theorems.Thm_Subring_coe_det
import Theorems.Thm_Subring_coe_map_inv_mul_map
import Theorems.Thm_Subring_coe_map_mul_map_inv
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
import Theorems.Thm_cartanDiag_inv
import Theorems.Thm_cartanDiag_zero
import Theorems.Thm_conj_cartanDiag_one_one
import Theorems.Thm_conj_cartanDiag_one_zero
import Theorems.Thm_conj_cartanDiag_zero_one
import Theorems.Thm_conj_cartanDiag_zero_zero
import Theorems.Thm_irreducible_zpow_mem_subring_iff
import Theorems.Thm_valuation_irreducible_zpow_eq_one_iff
import Theorems.Thm_valuation_isUnit
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
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}
theorem _root_.solution (x a : GL (Fin k) R) (f f' : Fin k → ℤ)
    (hax : cartanDiag ϖ hϖ f * a * (cartanDiag ϖ hϖ f')⁻¹ = x) :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by
  have hadetunit : IsUnit a.val.det := Matrix.isUnits_det_units a
  have hxdetunit : IsUnit x.val.det := Matrix.isUnits_det_units x
  have : (cartanDiag ϖ hϖ f * a * (cartanDiag ϖ hϖ f')⁻¹).val.det = x.val.det := by
    rw [hax]
    simp
  simp only [«GL».map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
    Matrix.coe_units_inv, Units.val_mul, val_cartanDiag, Matrix.det_mul, Matrix.det_diagonal,
    Subring.coe_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
  apply congrArg v at this
  simp only [map_mul] at this
  rw [valuation_isUnit x.val.det hxdetunit, valuation_isUnit a.val.det hadetunit] at this
  simp only [mul_one] at this
  rw [← map_mul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib] at this
  simp_rw [← zpow_neg] at this
  have hϖnezero : ϖ.val ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact hϖ.ne_zero
  have hsumzero' : Finset.univ.sum (fun i ↦ f i - f' i) = 0 := by
    rw [← valuation_irreducible_zpow_eq_one_iff (hϖ := hϖ)]
    rw [← Finset.prod_zpow_eq_zpow_sum (ha := hϖnezero)]
    rw [← this]
    congr
    ext i
    rw [← zpow_add₀ hϖnezero]
    rfl
  have : ∃ (σ : Equiv.Perm (Fin k)),
      IsUnit ((Equiv.Perm.sign σ) * Finset.univ.prod (fun i ↦ a (σ i) i)) := by
    rw [Matrix.det_apply'] at hadetunit
    obtain ⟨σ, _, hσ⟩ := IsLocalRing.exists_isUnit_of_isUnit_sum hadetunit
    use σ
  have : ∃ (σ : Equiv.Perm (Fin k)), ∀ i, IsUnit (a (σ i) i) := by
    obtain ⟨σ, hσ⟩ := this
    rw [IsUnit.mul_iff] at hσ
    simp_rw [IsUnit.prod_iff] at hσ
    use σ
    intro i
    exact hσ.right i (Finset.mem_univ i)
  obtain ⟨σ, hσ⟩ := this
  have hxij (i j : Fin k) :
      x.val i j = ϖ.val ^ (f i - f' j) * a.val i j := by
    show R.subtype (x.val i j) = _
    rw [← GL.map_apply (f := R.subtype) i j x, ← hax, cartanDiag_inv]
    simp only [GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
      Matrix.coe_units_inv, Units.val_mul, val_cartanDiag, zpow_neg, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.map_apply, zpow_sub₀ hϖnezero]
    group
  have hgezero (i : Fin k) : f (σ i) - f' i ≥ 0 := by
    rw [← irreducible_zpow_mem_subring_iff (hϖ := hϖ)]
    have := congrArg v (hxij (σ i) i)
    simp only [map_mul] at this
    rw [valuation_isUnit (a.val (σ i) i) (hσ i)] at this
    simp only [mul_one] at this
    rw [mem_subring_iff_integer, ← this, ← mem_subring_iff_integer]
    exact (x.val (σ i) i).property
  have hsumzero : Finset.univ.sum (fun i ↦ f (σ i) - f' i) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.Perm.sum_comp]
    · rw [← Finset.sum_sub_distrib]
      exact hsumzero'
    · simp
  have hzero : ∀ i ∈ Finset.univ, f (σ i) - f' i = 0 := by
    rw [← Finset.sum_eq_zero_iff_of_nonneg]
    · exact hsumzero
    · intro i _
      exact hgezero i
  use σ
  ext i
  simpa using Int.eq_of_sub_eq_zero (hzero i (Finset.mem_univ i))
