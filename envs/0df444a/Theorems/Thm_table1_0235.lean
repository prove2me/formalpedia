-- Prove2me | Theorems.Thm_table1_0235
-- name    : table1_0235
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:05.321082+00:00
-- url     : https://prove2.me/theorems/c79311c8-f872-469c-ac3d-1caf6ca8cac0
-- title:
--   table1 0235: table1 0235
-- statement:
--   {0,2,3,5}: blocks [0,0,1,1,2,2] (r=6), [0,0,0,1,1,2,2] (r+1=7). Frobenius: m ≥ 30.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L501-L503
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L501-L503

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem table1_0235 (hm : m ≥ 30) : HasPolychromColouring (Fin 3) ({0, 2, 3, 5} : Finset (ZMod m)) := by sorry
