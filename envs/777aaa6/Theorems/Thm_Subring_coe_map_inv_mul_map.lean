-- Prove2me | Theorems.Thm_Subring_coe_map_inv_mul_map
-- name    : Subring.coe_map_inv_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:05.834502+00:00
-- url     : https://prove2.me/theorems/8340c124-414b-442c-889f-152a782b2b25
-- title:
--   Subring: coe map inv mul map
-- statement:
--   The Subring construction uses the coe map inv mul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L115-L117
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L115-L117

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)

theorem Subring.coe_map_inv_mul_map (g : GL α R) :
    g.val⁻¹.map Subtype.val * g.val.map Subtype.val = 1 := by sorry
