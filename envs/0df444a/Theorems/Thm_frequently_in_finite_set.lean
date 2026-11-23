-- Prove2me | Theorems.Thm_frequently_in_finite_set
-- name    : frequently_in_finite_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:33.912677+00:00
-- url     : https://prove2.me/theorems/a1801888-4ece-4bb8-9f4e-8438d0400003
-- title:
--   frequently in finite set: frequently in finite set
-- statement:
--   Note that only the → direction needs the finiteness assumption.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L43-L58
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L43-L58

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem frequently_in_finite_set {X : Type*} [Finite X] {s : Set X} {xs : Stream' X} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x := by sorry
