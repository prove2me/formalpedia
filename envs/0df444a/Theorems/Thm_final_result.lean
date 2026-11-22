-- Prove2me | Theorems.Thm_final_result
-- name    : final_result
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:56:18.344236+00:00
-- url     : https://prove2.me/theorems/1dec6411-9239-404e-8b82-d472852a2367
-- title:
--   final result: final result
-- statement:
--   Every set `S` of 4 integers has a 3-polychromatic colouring.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Main.lean#L25-L34
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Main.lean#L25-L34

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Compute
import Definitions.Def_Polychromatic_FourThree_Combi
import Definitions.Def_Polychromatic_Main
set_option autoImplicit true

theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S := by sorry
