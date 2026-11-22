-- Prove2me | Theorems.Thm_lt_straussFunction_of_polychromNumber
-- name    : lt_straussFunction_of_polychromNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:33.859636+00:00
-- url     : https://prove2.me/theorems/49facf5d-1de0-4a0f-bcd8-f70f97c8bcc5
-- title:
--   lt strauss Function of polychrom Number: lt strauss Function of polychrom Number
-- statement:
--   The lt strauss Function of polychrom Number construction uses the lt strauss Function of polychrom Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L86-L91
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L86-L91

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem lt_straussFunction_of_polychromNumber {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : polychromNumber S < k) :
    #S < straussFunction k := by sorry
