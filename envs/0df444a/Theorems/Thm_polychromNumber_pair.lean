-- Prove2me | Theorems.Thm_polychromNumber_pair
-- name    : polychromNumber_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:31.901592+00:00
-- url     : https://prove2.me/theorems/1eb0c8b4-7806-4acd-86a2-0bfb467c3c46
-- title:
--   polychrom Number pair: polychrom Number pair
-- statement:
--   The polychrom Number pair construction uses the polychrom Number pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L244-L249
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L244-L249

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_pair [DecidableEq G] [IsAddTorsionFree G] {x y : G} (hxy : x ≠ y) :
    polychromNumber {x, y} = 2 := by sorry
