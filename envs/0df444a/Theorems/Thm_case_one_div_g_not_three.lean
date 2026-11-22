-- Prove2me | Theorems.Thm_case_one_div_g_not_three
-- name    : case_one_div_g_not_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:25.78155+00:00
-- url     : https://prove2.me/theorems/5e75804d-0d6d-4038-bec4-41ea583c3d64
-- title:
--   case one div g not three: case one div g not three
-- statement:
--   (1d), g ≢ 0 (mod 3): the periodic coloring 012012...012 works because
--       each translate of {0,1,g,g+1} hits all 3 residue classes mod 3.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L705-L716
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L705-L716

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_div_g_not_three (g : ℕ) (h_div : m = 3 * g ∨ m = 3 * g + 3) (hg3 : g % 3 ≠ 0) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
