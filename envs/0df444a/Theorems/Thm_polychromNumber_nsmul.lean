-- Prove2me | Theorems.Thm_polychromNumber_nsmul
-- name    : polychromNumber_nsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:44:40.345555+00:00
-- url     : https://prove2.me/theorems/6e39b21b-8271-4d4a-be6c-287f61d13b74
-- title:
--   polychrom Number nsmul: polychrom Number nsmul
-- statement:
--   The polychrom Number nsmul construction uses the polychrom Number nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L210-L212
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L210-L212

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_nsmul [DecidableEq G] [IsAddTorsionFree G] {k : ℕ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S := by sorry
