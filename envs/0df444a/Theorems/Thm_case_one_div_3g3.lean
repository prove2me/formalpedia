-- Prove2me | Theorems.Thm_case_one_div_3g3
-- name    : case_one_div_3g3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:36.220981+00:00
-- url     : https://prove2.me/theorems/76a227dd-0388-4ce5-9d92-ce04dbf9b0c2
-- title:
--   case one div 3g3: case one div 3g3
-- statement:
--   (1d), m = 3g+3, g ≡ 0 (mod 3): reversed diagonal coloring of period `g+1`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L765-L815
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L765-L815

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_div_3g3 (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
