-- Prove2me | Theorems.Thm_polychromNumber_zmod
-- name    : polychromNumber_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:54.405602+00:00
-- url     : https://prove2.me/theorems/dcb14807-3eac-4254-97c8-45f243268753
-- title:
--   polychrom Number zmod: polychrom Number zmod
-- statement:
--   Auxiliary: the polychromatic number is invariant under the translation that
--       maps `{0, a, b, c}` to `zmod_set m a b`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L46-L57
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L46-L57

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise

theorem polychromNumber_zmod {a b c : ℤ} {m : ℕ} (hm : m = c - a + b) :
    polychromNumber (({0, a, b, c} : Finset ℤ).image Int.cast : Finset (ZMod m)) =
      polychromNumber (zmod_set m a b) := by sorry
