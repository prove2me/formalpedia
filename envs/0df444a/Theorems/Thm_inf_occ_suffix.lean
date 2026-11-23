-- Prove2me | Theorems.Thm_inf_occ_suffix
-- name    : inf_occ_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:32.366801+00:00
-- url     : https://prove2.me/theorems/67c322f1-9bd4-4b10-b7f3-50060a095f12
-- title:
--   inf occ suffix: inf occ suffix
-- statement:
--   Removing any finite prefix of `xs` does not change `InfOcc xs`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L62-L68
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L62-L68

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem inf_occ_suffix {X : Type*} (xs : Stream' X) (k : ℕ) :
    InfOcc (xs.drop k) = InfOcc xs := by sorry
