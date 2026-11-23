-- Prove2me | Theorems.Thm_inf_occ_pair
-- name    : inf_occ_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:37:29.258992+00:00
-- url     : https://prove2.me/theorems/bee3b597-8c68-436a-bae9-51c47317af64
-- title:
--   inf occ pair: inf occ pair
-- statement:
--   Same as inf_acc_proj, but for pair types.  This result does follow from
--   inf_occ_proj, but that proof (see below) turns out to be longer.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L104-L127
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L104-L127

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem inf_occ_pair {X1 X2 : Type*} [Finite X1] [Finite X2] (xs : Stream' (X1 × X2)) :
    fst '' (InfOcc xs) = InfOcc (fst ∘ xs) ∧
    snd '' (InfOcc xs) = InfOcc (snd ∘ xs) := by sorry
