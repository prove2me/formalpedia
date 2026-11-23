-- Prove2me | Theorems.Thm_infOcc_comp_of_injective
-- name    : infOcc_comp_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:37:37.906684+00:00
-- url     : https://prove2.me/theorems/684953e9-f426-4591-901e-5f745b9de2cd
-- title:
--   inf Occ comp of injective: inf Occ comp of injective
-- statement:
--   The inf Occ comp of injective construction uses the inf Occ comp of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L132-L140
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L132-L140

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem infOcc_comp_of_injective {α β : Type*} {f : α → β} (hf : f.Injective) (xs : Stream' α) :
    InfOcc (f ∘ xs) = f '' InfOcc xs := by sorry
