-- Prove2me | Theorems.Thm_polychromNumber_subgroup
-- name    : polychromNumber_subgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:13.679505+00:00
-- url     : https://prove2.me/theorems/9eb8af0f-32f7-45f0-8631-ef0cd9aad3ed
-- title:
--   polychrom Number subgroup: polychrom Number subgroup
-- statement:
--   The polychrom Number subgroup construction uses the polychrom Number subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L159-L192
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L159-L192

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_subgroup [DecidableEq G] (H : AddSubgroup G) {S : Finset H} :
    polychromNumber S = polychromNumber (G := G) (S.image H.subtype) := by sorry
