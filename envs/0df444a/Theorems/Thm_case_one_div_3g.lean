-- Prove2me | Theorems.Thm_case_one_div_3g
-- name    : case_one_div_3g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:24.270361+00:00
-- url     : https://prove2.me/theorems/1d854d11-4ed8-4255-8f6b-80df54a0d25e
-- title:
--   case one div 3g: case one div 3g
-- statement:
--   (1d), m = 3g, g ≡ 0 (mod 3): diagonal coloring `n ↦ (n%3 + n/g) % 3`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L719-L762
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L719-L762

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_div_3g (g : ℕ) (hm_eq : m = 3 * g) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
