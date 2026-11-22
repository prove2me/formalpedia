-- Prove2me | solution 1 for GL.map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:09.193183+00:00
-- url     : https://prove2.me/submissions/a78f58aa-bed6-490e-a6cd-a2b9e0230f3a

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
theorem _root_.solution (g : GL α R) : GL.map f g⁻¹ = (GL.map f g)⁻¹ := by
  ext
  simp
end «GL»
