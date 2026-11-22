-- Prove2me | solution 1 for Submodule.span_eq_top_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:56:39.154198+00:00
-- url     : https://prove2.me/submissions/6d983477-ba41-48a3-acaa-f342845ddd04

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
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
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]
omit [IsPrincipalIdealRing ↥R]
namespace Submodule
theorem _root_.solution {M : Submodule R (ι → K)} (h : Module.rank R M = Fintype.card ι) :
    Submodule.span K (M : Set (ι → K)) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' M.subtype (Submodule.ker_subtype M)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  rw [h, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ x.val.val) ⊆ M := by
    rintro x ⟨a, rfl⟩
    simp
  have hcard : Fintype.card ↑s = Module.finrank K (ι → K) := by
    rw [hcard, Module.finrank_fintype_fun_eq_card K]
  rw [_root_.eq_top_iff]
  rw [← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset
end Submodule
