-- Prove2me | solution 1 for Basis.toGL_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:57:29.899616+00:00
-- url     : https://prove2.me/submissions/d49e90e4-da83-4143-a991-b51864efa891

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
import Theorems.Thm_Matrix_GeneralLinearGroup_mem_toSubmodule
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
open Basis
variable [Fintype ι] [DecidableEq ι]
namespace Basis
theorem _root_.solution {M : Submodule R (ι → K)} [IsLattice M] (b : Basis ι R M) :
    (Basis.toGL b).toSubmodule = M := by
  ext x
  simp only [Matrix.GeneralLinearGroup.mem_toSubmodule]
  constructor
  · rintro ⟨y, hy, rfl⟩
    let bs : Basis ι R (ι → R) := Pi.basisFun R ι
    have hym : y ∈ Submodule.span R (Set.range bs) := by simp
    induction' hym using Submodule.span_induction with y hym y z _ _ hym hzm a y _ hym
    · obtain ⟨i, rfl⟩ := hym
      simp [bs]
      change (fun j => b.toGL j i) ∈ M
      simpa only [toGL_apply] using (b i).property
    · simp
    · simp only [Subtype.val_comp_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ hym hzm
    · simp only [Subtype.val_comp_smul]
      change (b.toGL).val.mulVec ((a : K) • (Subtype.val ∘ y)) ∈ M
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ a hym
  · intro hx
    rw [Basis.mem_submodule_iff' b] at hx
    obtain ⟨c, rfl⟩ := hx
    use c
    show (b.toGL).val.mulVec (fun i ↦ c i) = _
    unfold Matrix.mulVec
    unfold dotProduct
    ext j
    simp only [Basis.toGL_apply, Finset.sum_apply, Pi.smul_apply]
    congr
    ext i
    rw [mul_comm]
    rfl
end Basis
