-- Prove2me | Theorems.Thm_table1_0123
-- name    : table1_0123
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:06.363711+00:00
-- url     : https://prove2.me/theorems/3a0ec966-1747-413e-b7de-8a7054d9d95a
-- title:
--   table1 0123: table1 0123
-- statement:
--   {0,1,2,3}: blocks [0,1,2] (r=3), [0,0,1,2] (r+1=4). Frobenius bound: m ≥ 6.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L491-L493
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L491-L493

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0123 (hm : m ≥ 6) : HasPolychromColouring (Fin 3) ({0, 1, 2, 3} : Finset (ZMod m)) := by sorry
