-- Prove2me | Theorems.Thm_case_one_dispatch
-- name    : case_one_dispatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:32.687573+00:00
-- url     : https://prove2.me/theorems/a730c5b4-7d15-4ae6-9905-459c3171f989
-- title:
--   case one dispatch: case one dispatch
-- statement:
--   **Case 1 combined dispatch:** applies subcases (1a)–(1d) for 2 ≤ g ≤ m/2 and m ≥ 289.
--       This is the main lemma for the single-cycle case, assuming the set has already been
--       reduced to the form {0, 1, g, g+1}.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L833-L882
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L833-L882

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g) (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
