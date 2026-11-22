-- Prove2me | Theorems.Thm_GL_map_inv_mul_map
-- name    : GL.map_inv_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:55.213018+00:00
-- url     : https://prove2.me/theorems/eaa4a4a1-50a1-44c5-8bfd-738f5218176d
-- title:
--   GL: map inv mul map
-- statement:
--   The GL construction uses the map inv mul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L59-L65
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L59-L65

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.map_inv_mul_map (g : GL α R) : GL.map f g⁻¹ * GL.map f g = 1 := by sorry
