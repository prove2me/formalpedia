-- Prove2me | Theorems.Thm_polychromNumber_subset
-- name    : polychromNumber_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:44.216443+00:00
-- url     : https://prove2.me/theorems/14cbf5dc-49c3-48af-a4be-d144750a5640
-- title:
--   polychrom Number subset: polychrom Number subset
-- statement:
--   The polychrom Number subset construction uses the polychrom Number subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L113-L117
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L113-L117

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_subset {S' : Finset G} (hS' : S' ⊆ S) :
    polychromNumber S' ≤ polychromNumber S := by sorry
