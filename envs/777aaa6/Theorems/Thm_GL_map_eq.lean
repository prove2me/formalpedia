-- Prove2me | Theorems.Thm_GL_map_eq
-- name    : GL_map_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:41.893189+00:00
-- url     : https://prove2.me/theorems/7e810318-94a4-491a-bebe-cd3e89385689
-- title:
--   GL map eq: GL map eq
-- statement:
--   The GL map eq construction uses the GL map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L77-L80
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L77-L80

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL_map_eq {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R S : Type*} [CommRing R] [CommRing S] (g : GL ι R) (f : R →+* S) :
    GL.map f g = Matrix.GeneralLinearGroup.map f g := by sorry
