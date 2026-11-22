-- Prove2me | solution 1 for GL.mem_range_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:46:28.303669+00:00
-- url     : https://prove2.me/submissions/91075633-e1e4-4687-8d8e-881faf981835

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_det
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
import Theorems.Thm_GL_coe_map_inv_mul_map
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv
attribute [local simp] GL.coe_map_inv_mul_map

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution {f : R →+* S} (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι S) :
    g ∈ Set.range (Matrix.GeneralLinearGroup.map f) ↔
      (∀ (i j : ι), g i j ∈ Set.range f) ∧
        ↑g.det⁻¹ ∈ Set.range f := by
  refine ⟨fun ⟨k, hk⟩ ↦ hk ▸ by simp [Matrix.GeneralLinearGroup.map_det], fun ⟨h1, ⟨u, hu⟩⟩ ↦ ?_⟩
  choose r hr using h1
  refine ⟨.mk'' r ?_, by ext; simp [Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, hr]⟩
  rw [isUnit_iff_exists_inv]
  use u
  apply hf
  simp only [_root_.map_mul, RingHom.map_det, RingHom.mapMatrix_apply, _root_.map_one]
  rw [hu]
  convert (Matrix.GeneralLinearGroup.det g).val_inv using 2
  congr; ext; simp [hr]
end «GL»
