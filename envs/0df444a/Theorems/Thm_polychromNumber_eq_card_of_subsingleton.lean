-- Prove2me | Theorems.Thm_polychromNumber_eq_card_of_subsingleton
-- name    : polychromNumber_eq_card_of_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:44.931079+00:00
-- url     : https://prove2.me/theorems/e40b5c00-2459-4015-98aa-fb9eec0445c8
-- title:
--   polychrom Number eq card of subsingleton: polychrom Number eq card of subsingleton
-- statement:
--   The polychrom Number eq card of subsingleton construction uses the polychrom Number eq card of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L122-L128
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L122-L128

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_eq_card_of_subsingleton (hS : (S : Set G).Subsingleton) :
    polychromNumber S = #S := by sorry
