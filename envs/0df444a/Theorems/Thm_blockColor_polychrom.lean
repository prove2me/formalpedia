-- Prove2me | Theorems.Thm_blockColor_polychrom
-- name    : blockColor_polychrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:48.856458+00:00
-- url     : https://prove2.me/theorems/3f710cf0-bd65-40f4-af99-3157575230d8
-- title:
--   block Color polychrom: block Color polychrom
-- statement:
--   **Key infrastructure theorem.** If all block-pair checks pass, the block coloring is
--       polychromatic for any m expressible as rA·h + rB·k. This is the main interface
--       used by the Table 1 lemmas below.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L401-L443
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L401-L443

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise

theorem blockColor_polychrom
    (A B : List (Fin 3)) (offsets : List ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hpairs : checkBlockPairs offsets A B = true)
    {h k : ℕ} (hhk : 0 < h + k) {m : ℕ}
    (hm : A.length * h + B.length * k = m)
    {i : ℕ} (hi : i < m) (c : Fin 3) :
    ∃ s ∈ offsets, blockColorVal A B h ((i + s) % m) = c := by sorry
