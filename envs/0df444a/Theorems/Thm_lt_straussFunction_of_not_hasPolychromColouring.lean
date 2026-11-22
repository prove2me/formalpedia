-- Prove2me | Theorems.Thm_lt_straussFunction_of_not_hasPolychromColouring
-- name    : lt_straussFunction_of_not_hasPolychromColouring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:49.964465+00:00
-- url     : https://prove2.me/theorems/acc3dec6-6939-4fa2-b309-acfae8db6677
-- title:
--   lt strauss Function of not has Polychrom Colouring: lt strauss Function of not has Polychrom Colouring
-- statement:
--   The lt strauss Function of not has Polychrom Colouring construction uses the lt strauss Function of not has Polychrom Colouring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L80-L84
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L80-L84

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem lt_straussFunction_of_not_hasPolychromColouring {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : ¬ HasPolychromColouring (Fin k) S) :
    #S < straussFunction k := by sorry
