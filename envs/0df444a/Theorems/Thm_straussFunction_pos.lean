-- Prove2me | Theorems.Thm_straussFunction_pos
-- name    : straussFunction_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:52.831174+00:00
-- url     : https://prove2.me/theorems/dd32d867-3c9e-465b-8860-b23fe6cde5a1
-- title:
--   strauss Function pos: strauss Function pos
-- statement:
--   The strauss Function pos construction uses the strauss Function pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L76-L78
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L76-L78

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_pos {k : ℕ} (hk : k ≠ 0) : 0 < straussFunction k := by sorry
