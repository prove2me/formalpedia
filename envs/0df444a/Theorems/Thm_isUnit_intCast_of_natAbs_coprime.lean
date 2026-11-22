-- Prove2me | Theorems.Thm_isUnit_intCast_of_natAbs_coprime
-- name    : isUnit_intCast_of_natAbs_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:50.222181+00:00
-- url     : https://prove2.me/theorems/d3a3742f-e37f-4f46-8ffe-61b79c71d0a8
-- title:
--   is Unit int Cast of nat Abs coprime: is Unit int Cast of nat Abs coprime
-- statement:
--   The is Unit int Cast of nat Abs coprime construction uses the is Unit int Cast of nat Abs coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L526-L531
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/BlockColour.lean#L526-L531

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Mathlib.Algebra.Ring.AddAut
import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise

theorem isUnit_intCast_of_natAbs_coprime {n : ℕ} {b : ℤ}
    (h : Nat.gcd b.natAbs n = 1) :
    IsUnit (Int.cast b : ZMod n) := by sorry
