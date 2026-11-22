-- Prove2me | Theorems.Thm_le_straussFunction_self
-- name    : le_straussFunction_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:52.487169+00:00
-- url     : https://prove2.me/theorems/8dcdc65d-29fe-45c0-b9ab-860da2efb232
-- title:
--   le strauss Function self: le strauss Function self
-- statement:
--   The le strauss Function self construction uses the le strauss Function self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L95-L104
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L95-L104

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem le_straussFunction_self {k : ℕ} :
    k ≤ straussFunction k := by sorry
