-- Prove2me | Theorems.Thm_polychromNumber_image
-- name    : polychromNumber_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:52.608496+00:00
-- url     : https://prove2.me/theorems/90245803-139b-4ff8-b74d-398059ba6808
-- title:
--   polychrom Number image: polychrom Number image
-- statement:
--   The polychrom Number image construction uses the polychrom Number image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L138-L143
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L138-L143

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_image {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F) {S : Finset G} :
    polychromNumber (S.image φ) ≤ polychromNumber S := by sorry
