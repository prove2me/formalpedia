-- Prove2me | solution 1 for GL.map_inv_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:58.269875+00:00
-- url     : https://prove2.me/submissions/75957e7e-fa5b-4457-9171-400722991332

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one
attribute [local simp] GL.map_mul_map_inv

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g : GL α R) : GL.map f g⁻¹ * GL.map f g = 1 := by
  apply Units.ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv, inv_inv,
    Units.val_mul, Units.val_one]
  show f.mapMatrix g.val⁻¹ * f.mapMatrix g.val = 1
  rw [← _root_.map_mul]
  simp
end «GL»
