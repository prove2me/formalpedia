-- Prove2me | Theorems.Thm_case_one_complement
-- name    : case_one_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:47.149666+00:00
-- url     : https://prove2.me/theorems/1fbd57e9-55ad-4185-b74e-b935ed81beed
-- title:
--   case one complement: case one complement
-- statement:
--   Auxiliary: WLOG g ≤ m/2, since {0,1,m-g,m-g+1} = (-g) +ᵥ {0,1,g,g+1}.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L887-L896
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L887-L896

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_complement (g : ℕ) (hg : g < m) : HasPolychromColouring (Fin 3)
      ({0, 1, (↑(m - g) : ZMod m), (↑(m - g) : ZMod m) + 1} : Finset (ZMod m)) ↔
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
