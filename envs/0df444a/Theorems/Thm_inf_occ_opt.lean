-- Prove2me | Theorems.Thm_inf_occ_opt
-- name    : inf_occ_opt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:37:57.057658+00:00
-- url     : https://prove2.me/theorems/8bc3fcc6-b456-4a7e-86d8-33d195d93622
-- title:
--   inf occ opt: inf occ opt
-- statement:
--   The inf occ opt construction uses the inf occ opt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L172-L189
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L172-L189

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem inf_occ_opt {X : Type*} [Finite X] (os : Stream' (Option X)) (y : X)
    (h : ∀ o ∈ InfOcc os, o.isSome) :
    {x | ∃ o ∈ InfOcc os, o = some x} = InfOcc ((getD · y) ∘ os) := by sorry
