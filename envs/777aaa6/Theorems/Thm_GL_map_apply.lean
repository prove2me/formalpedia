-- Prove2me | Theorems.Thm_GL_map_apply
-- name    : GL.map_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:48.812555+00:00
-- url     : https://prove2.me/theorems/de494b19-d2cb-4da2-bc99-ff4388166cc5
-- title:
--   GL: map apply
-- statement:
--   The GL construction uses the map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L24-L25
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L24-L25

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem GL.map_apply (i j : α) (g : GL α R) : GL.map f g i j = f (g i j) := by sorry
