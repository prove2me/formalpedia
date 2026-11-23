-- Prove2me | Theorems.Thm_inf_occ_eventually
-- name    : inf_occ_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:17:55.682795+00:00
-- url     : https://prove2.me/theorems/328d80e7-dacc-4558-9ac8-ffccfe8d4202
-- title:
--   inf occ eventually: inf occ eventually
-- statement:
--   Over a finite type, `xs k` is in `InfOcc xs` for all sufficiently large `k`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L72-L84
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L72-L84

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem inf_occ_eventually {X : Type*} [Finite X] (xs : Stream' X) :
    ∀ᶠ k in atTop, xs k ∈ InfOcc xs := by sorry
