-- Prove2me | Theorems.Thm_polychromNumber_zsmul
-- name    : polychromNumber_zsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:50.007707+00:00
-- url     : https://prove2.me/theorems/0711ef74-d932-41b8-8def-8ce1959f380a
-- title:
--   polychrom Number zsmul: polychrom Number zsmul
-- statement:
--   The polychrom Number zsmul construction uses the polychrom Number zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L214-L216
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L214-L216

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_zsmul [DecidableEq G] [IsAddTorsionFree G] {k : ℤ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S := by sorry
