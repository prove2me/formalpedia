-- Prove2me | Theorems.Thm_case_one_small_g
-- name    : case_one_small_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:25.92627+00:00
-- url     : https://prove2.me/theorems/32fe29e9-9052-4fff-87a4-fe9baf34c959
-- title:
--   case one small g: case one small g
-- statement:
--   **Subcase (1a):** g ∈ {2, 3, 4}. Reduces directly to Table 1 entries.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L32-L37
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L32-L37

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_small_g (g : ℕ) (hm : m ≥ 289) (hg : g ∈ ({2, 3, 4} : Finset ℕ)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
