-- Prove2me | Theorems.Thm_straussFunction_zero
-- name    : straussFunction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:57.184793+00:00
-- url     : https://prove2.me/theorems/914cafbd-6ead-4c12-ad00-8143005de02f
-- title:
--   strauss Function zero: strauss Function zero
-- statement:
--   The strauss Function zero construction uses the strauss Function zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L41-L47
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L41-L47

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_zero : straussFunction 0 = 0 := by sorry
