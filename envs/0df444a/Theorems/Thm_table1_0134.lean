-- Prove2me | Theorems.Thm_table1_0134
-- name    : table1_0134
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:23.031719+00:00
-- url     : https://prove2.me/theorems/f21aff56-a552-42eb-ba6f-22538f130285
-- title:
--   table1 0134: table1 0134
-- statement:
--   {0,1,3,4}: blocks [0,0,1,2,1,2] (r=6), [0,0,0,1,2,1,2] (r+1=7). Frobenius: m ≥ 30.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L496-L498
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L496-L498

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0134 (hm : m ≥ 30) : HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod m)) := by sorry
