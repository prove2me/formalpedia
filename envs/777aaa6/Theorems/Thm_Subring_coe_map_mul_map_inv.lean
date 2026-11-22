-- Prove2me | Theorems.Thm_Subring_coe_map_mul_map_inv
-- name    : Subring.coe_map_mul_map_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:50.948183+00:00
-- url     : https://prove2.me/theorems/2dd5e5d2-38ed-410e-a3e3-0dd212e87707
-- title:
--   Subring: coe map mul map inv
-- statement:
--   The Subring construction uses the coe map mul map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L110-L112
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/RingHom.lean#L110-L112

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)

theorem Subring.coe_map_mul_map_inv (g : GL α R) :
    g.val.map Subtype.val * g.val⁻¹.map Subtype.val = 1 := by sorry
