-- Prove2me | Theorems.Thm_one_le_polychromNumber
-- name    : one_le_polychromNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:52.108188+00:00
-- url     : https://prove2.me/theorems/46978446-625e-420b-bf8a-251a60fc73a6
-- title:
--   one le polychrom Number: one le polychrom Number
-- statement:
--   The one le polychrom Number construction uses the one le polychrom Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L73-L74
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L73-L74

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem one_le_polychromNumber (hS : S.Nonempty) : 1 ≤ polychromNumber S := by sorry
