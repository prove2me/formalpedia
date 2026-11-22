-- Prove2me | Theorems.Thm_straussFunction_le_of_forall_mBound
-- name    : straussFunction_le_of_forall_mBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:57.047912+00:00
-- url     : https://prove2.me/theorems/3fc1c31f-a867-4d89-be1e-4390a89377f1
-- title:
--   strauss Function le of forall m Bound: strauss Function le of forall m Bound
-- statement:
--   The strauss Function le of forall m Bound construction uses the strauss Function le of forall m Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L139-L140
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L139-L140

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset

theorem straussFunction_le_of_forall_mBound {k : ℕ} (hk : 4 ≤ k) : straussFunction k ≤ mBound k := by sorry
