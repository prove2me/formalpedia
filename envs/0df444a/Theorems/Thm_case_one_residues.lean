-- Prove2me | Theorems.Thm_case_one_residues
-- name    : case_one_residues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:23.290202+00:00
-- url     : https://prove2.me/theorems/732ed7e5-9227-4bd6-8b69-12ac330f4d29
-- title:
--   case one residues: case one residues
-- statement:
--   **Subcase (1c):** dispatches on `m mod (3g)` to reduce to Table 1 sets via ×3.
--       Covers the case `3 ∤ m` with `2⌊m/6⌋ ≤ g ≤ ⌈m/3⌉` (paper §4.1).
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L638-L689
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L638-L689

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem case_one_residues (g : ℕ) (hm : m ≥ 289) (h_res : m % 3 ≠ 0)
    (h_range : 2 * (m / 6) ≤ g ∧ g ≤ (m + 2) / 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by sorry
