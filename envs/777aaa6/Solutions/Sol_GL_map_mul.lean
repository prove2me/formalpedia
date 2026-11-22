-- Prove2me | solution 1 for GL.map_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:42:27.997546+00:00
-- url     : https://prove2.me/submissions/c4778eba-5f11-4d57-9dfc-5f8d8e9cb6db

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g h : GL α R) : GL.map f (g * h) = GL.map f g * GL.map f h := by
  ext
  simp
end «GL»
