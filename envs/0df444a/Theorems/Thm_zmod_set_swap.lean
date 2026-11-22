-- Prove2me | Theorems.Thm_zmod_set_swap
-- name    : zmod_set_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:20.182329+00:00
-- url     : https://prove2.me/theorems/f2415872-c94f-412d-a5fa-e7ab81f6d8c6
-- title:
--   zmod set swap: zmod set swap
-- statement:
--   The set {0, b-a, b, 2b-a} is symmetric in the two repeated differences b and b-a:
--       swapping them (replacing a by -a, b by b-a) gives the same set.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L61-L62
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L61-L62

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise

theorem zmod_set_swap (m : ℕ) (a b : ℤ) : zmod_set m (-a) (b - a) = zmod_set m a b := by sorry
