-- Prove2me | Theorems.Thm_GL_coe_map_inv_mul_map
-- name    : GL.coe_map_inv_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:03.09373+00:00
-- url     : https://prove2.me/theorems/9ce09577-b145-406f-9aaa-7f562135ae59
-- title:
--   GL: coe map inv mul map
-- statement:
--   The GL construction uses the coe map inv mul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L73-L75
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L73-L75

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.coe_map_inv_mul_map (g : GL α R) : g.val⁻¹.map f * g.val.map f = 1 := by sorry
