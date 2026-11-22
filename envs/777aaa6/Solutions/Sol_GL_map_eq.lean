-- Prove2me | solution 1 for GL_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:52:38.062409+00:00
-- url     : https://prove2.me/submissions/1f9d5dea-e872-4702-bc85-533ccd936c63

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
theorem _root_.solution {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R S : Type*} [CommRing R] [CommRing S] (g : GL ι R) (f : R →+* S) :
    GL.map f g = Matrix.GeneralLinearGroup.map f g :=
  rfl
