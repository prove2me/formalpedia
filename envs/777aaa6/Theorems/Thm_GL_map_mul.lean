-- Prove2me | Theorems.Thm_GL_map_mul
-- name    : GL.map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:16.087946+00:00
-- url     : https://prove2.me/theorems/d1727133-7d81-4252-b8c7-c6bef3a0ed27
-- title:
--   GL: map mul
-- statement:
--   The GL construction uses the map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L33-L35
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L33-L35

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.map_mul (g h : GL α R) : GL.map f (g * h) = GL.map f g * GL.map f h := by sorry
