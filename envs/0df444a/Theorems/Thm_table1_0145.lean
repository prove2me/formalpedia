-- Prove2me | Theorems.Thm_table1_0145
-- name    : table1_0145
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:21.162321+00:00
-- url     : https://prove2.me/theorems/9b5ccfbb-ba73-407e-8b8a-deffe608b2ee
-- title:
--   table1 0145: table1 0145
-- statement:
--   {0,1,4,5}: blocks [0,0,0,1,2,1,2] (r=7), [0,0,0,0,1,2,1,2] (r+1=8). Frobenius: m ≥ 42.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L518-L520
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L518-L520

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0145 (hm : m ≥ 42) : HasPolychromColouring (Fin 3) ({0, 1, 4, 5} : Finset (ZMod m)) := by sorry
