-- Prove2me | Theorems.Thm_GL_coe_map_mul_map_inv
-- name    : GL.coe_map_mul_map_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:56.999558+00:00
-- url     : https://prove2.me/theorems/09be1a89-0957-45f0-ad47-7983d8ece45d
-- title:
--   GL: coe map mul map inv
-- statement:
--   The GL construction uses the coe map mul map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L68-L70
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L68-L70

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.coe_map_mul_map_inv (g : GL α R) : g.val.map f * g.val⁻¹.map f = 1 := by sorry
