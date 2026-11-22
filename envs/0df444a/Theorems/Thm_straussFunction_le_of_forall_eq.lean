-- Prove2me | Theorems.Thm_straussFunction_le_of_forall_eq
-- name    : straussFunction_le_of_forall_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:43.869611+00:00
-- url     : https://prove2.me/theorems/f06ac289-2cb1-4075-adb5-3d8e72d6ed00
-- title:
--   strauss Function le of forall eq: strauss Function le of forall eq
-- statement:
--   The strauss Function le of forall eq construction uses the strauss Function le of forall eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L68-L74
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L68-L74

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_le_of_forall_eq {k m : ℕ}
    (h : ∀ S : Finset ℤ, #S = m → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m := by sorry
