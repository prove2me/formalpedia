-- Prove2me | Theorems.Thm_GL_map_mul_map_inv
-- name    : GL.map_mul_map_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:03.260987+00:00
-- url     : https://prove2.me/theorems/e34b1b80-7ce9-471f-b2c6-03b1a028ae30
-- title:
--   GL: map mul map inv
-- statement:
--   The GL construction uses the map mul map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L50-L56
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L50-L56

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.map_mul_map_inv (g : GL α R) : GL.map f g * GL.map f g⁻¹ = 1 := by sorry
