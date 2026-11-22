-- Prove2me | Theorems.Thm_table1_0347
-- name    : table1_0347
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:06.718603+00:00
-- url     : https://prove2.me/theorems/6043f1fd-59a5-4001-885b-e48729866f8d
-- title:
--   table1 0347: table1 0347
-- statement:
--   {0,3,4,7}: blocks [0,0,0,1,1,1,2,2,2] (r=9), [0,0,0,0,1,1,1,2,2,2] (r+1=10).
--       Frobenius: m ≥ 72.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L507-L509
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L507-L509

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0347 (hm : m ≥ 72) : HasPolychromColouring (Fin 3) ({0, 3, 4, 7} : Finset (ZMod m)) := by sorry
