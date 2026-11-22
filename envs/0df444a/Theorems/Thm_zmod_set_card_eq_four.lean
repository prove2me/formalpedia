-- Prove2me | Theorems.Thm_zmod_set_card_eq_four
-- name    : zmod_set_card_eq_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:03.644829+00:00
-- url     : https://prove2.me/theorems/f1778f37-32b1-490d-a1ce-9c9b710656ca
-- title:
--   zmod set card eq four: zmod set card eq four
-- statement:
--   Auxiliary: the set zmod_set m a b has 4 elements when 0 < a < b and 2b - a < m.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L68-L84
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L68-L84

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
set_option autoImplicit true
open Finset Pointwise

theorem zmod_set_card_eq_four {a b : ℤ} {m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbm : 2 * b - a < ↑m) :
    (zmod_set m a b).card = 4 := by sorry
