-- Prove2me | Theorems.Thm_polychromNumber_eq_card_of_card_le_two
-- name    : polychromNumber_eq_card_of_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:00.614431+00:00
-- url     : https://prove2.me/theorems/9ba34371-5cd4-4d71-baf6-9673e5e9c68e
-- title:
--   polychrom Number eq card of card le two: polychrom Number eq card of card le two
-- statement:
--   The polychrom Number eq card of card le two construction uses the polychrom Number eq card of card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L251-L259
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L251-L259

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_eq_card_of_card_le_two [IsAddTorsionFree G] {S : Finset G} (hS : #S ≤ 2) :
    polychromNumber S = #S := by sorry
