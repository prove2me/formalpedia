-- Prove2me | Theorems.Thm_straussFunction_le_of_forall
-- name    : straussFunction_le_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:55.10317+00:00
-- url     : https://prove2.me/theorems/7fee2313-265c-4f31-9aff-e549c022ba9d
-- title:
--   strauss Function le of forall: strauss Function le of forall
-- statement:
--   Upper bounds on the Strauss function.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L64-L66
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L64-L66

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_le_of_forall {k m : ℕ}
    (h : ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m := by sorry
