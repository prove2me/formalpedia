-- Prove2me | Theorems.Thm_table1_0358
-- name    : table1_0358
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:08.72669+00:00
-- url     : https://prove2.me/theorems/dde69255-be8a-4392-9213-3253c0cb457f
-- title:
--   table1 0358: table1 0358
-- statement:
--   {0,3,5,8}: blocks [0,0,0,1,1,1,2,2,2] (r=9), [0,0,0,0,1,1,1,2,2,2] (r+1=10).
--       Frobenius: m ≥ 72.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L513-L515
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L513-L515

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0358 (hm : m ≥ 72) : HasPolychromColouring (Fin 3) ({0, 3, 5, 8} : Finset (ZMod m)) := by sorry
