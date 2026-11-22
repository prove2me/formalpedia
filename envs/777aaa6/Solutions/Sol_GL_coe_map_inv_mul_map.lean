-- Prove2me | solution 1 for GL.coe_map_inv_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:45:40.348865+00:00
-- url     : https://prove2.me/submissions/6402c166-beab-43cb-8ffa-b2486a4b3f89

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_inv_mul_map
import Theorems.Thm_GL_coe_map_mul_map_inv
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_inv_mul_map
attribute [local simp] GL.coe_map_mul_map_inv

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g : GL α R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp
end «GL»
