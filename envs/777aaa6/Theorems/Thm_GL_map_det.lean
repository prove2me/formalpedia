-- Prove2me | Theorems.Thm_GL_map_det
-- name    : GL.map_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:22.635626+00:00
-- url     : https://prove2.me/theorems/0b2f9618-0c90-4855-aa80-9b4f5a8e03db
-- title:
--   GL: map det
-- statement:
--   The GL construction uses the map det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L41-L47
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L41-L47

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.map_det (g : GL α R) : Matrix.GeneralLinearGroup.det (GL.map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by sorry
