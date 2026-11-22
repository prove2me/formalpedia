-- Prove2me | solution 1 for GL.map_mul_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:02.317552+00:00
-- url     : https://prove2.me/submissions/f6547007-580f-4193-95fb-d56834afe282

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_map_mul
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g : GL α R) : GL.map f g * GL.map f g⁻¹ = 1 := by
  apply Units.ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv, inv_inv,
    Units.val_mul, Units.val_one]
  show f.mapMatrix g.val * f.mapMatrix g.val⁻¹ = 1
  rw [← _root_.map_mul]
  simp
end «GL»
