-- Prove2me | solution 1 for GL.map_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:40:53.938751+00:00
-- url     : https://prove2.me/submissions/3c470773-375e-4d6d-9b13-dfba180116c2

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (i j : α) (g : GL α R) : GL.map f g i j = f (g i j) := by
  simp
end «GL»
