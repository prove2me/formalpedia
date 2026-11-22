-- Prove2me | Theorems.Thm_straussFunction_spec
-- name    : straussFunction_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:34.319493+00:00
-- url     : https://prove2.me/theorems/560e1ad4-b6d4-47f6-a0ee-9156984a3a6d
-- title:
--   strauss Function spec: strauss Function spec
-- statement:
--   The strauss Function spec construction uses the strauss Function spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L57-L60
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L57-L60

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_spec {k : ℕ} (hk : k ≠ 0) (S : Finset ℤ)
    (hkS : straussFunction k ≤ #S) :
    HasPolychromColouring (Fin k) S := by sorry
