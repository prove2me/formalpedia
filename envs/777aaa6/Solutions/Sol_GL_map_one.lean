-- Prove2me | solution 1 for GL.map_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:41:31.106004+00:00
-- url     : https://prove2.me/submissions/a9b5d042-65d8-41f6-8c8c-eb4e351d44a6

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
attribute [local simp] GL.map_apply

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution : GL.map f (1 : GL α R) = 1 := by
  ext
  simp
end «GL»
