-- Prove2me | Theorems.Thm_polychromNumber_vadd
-- name    : polychromNumber_vadd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:07.407312+00:00
-- url     : https://prove2.me/theorems/ed9ca479-d1f1-4a7b-96cc-4a1eae53d029
-- title:
--   polychrom Number vadd: polychrom Number vadd
-- statement:
--   The polychromatic number is invariant under translation.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L52-L53
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L52-L53

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_vadd [DecidableEq G] {n : G} :
    polychromNumber (n +ᵥ S) = polychromNumber S := by sorry
