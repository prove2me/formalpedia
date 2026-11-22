-- Prove2me | solution 1 for GL.coe_map_mul_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:44:44.235979+00:00
-- url     : https://prove2.me/submissions/f4a1981a-7644-401f-90bc-06f6833cb08d

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
import Theorems.Thm_GL_map_mul
import Theorems.Thm_GL_map_mul_map_inv
import Theorems.Thm_GL_map_inv_mul_map
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one
attribute [local simp] GL.map_mul_map_inv
attribute [local simp] GL.map_inv_mul_map

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g : GL α R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp
end «GL»
