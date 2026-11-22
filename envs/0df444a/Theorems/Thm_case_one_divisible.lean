-- Prove2me | Theorems.Thm_case_one_divisible
-- name    : case_one_divisible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:29.7508+00:00
-- url     : https://prove2.me/theorems/d5102581-6a6b-45e3-bef4-3e17337503b9
-- title:
--   case one divisible: case one divisible
-- statement:
--   **Subcase (1d) assembled:** dispatches on `g % 3` and `m ∈ {3g, 3g+3}` (paper §4.1).
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L818-L824
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L818-L824

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_divisible (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
