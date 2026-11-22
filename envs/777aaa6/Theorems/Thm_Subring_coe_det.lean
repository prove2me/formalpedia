-- Prove2me | Theorems.Thm_Subring_coe_det
-- name    : Subring.coe_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:31.903461+00:00
-- url     : https://prove2.me/theorems/2ae6093e-c27f-48f5-a22d-ab9dcee29a83
-- title:
--   Subring: coe det
-- statement:
--   The Subring construction uses the coe det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L120-L122
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L120-L122

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)

theorem Subring.coe_det (g : Matrix α α R) : (g.map Subtype.val).det = g.det := by sorry
