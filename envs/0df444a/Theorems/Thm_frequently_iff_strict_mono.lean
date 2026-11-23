-- Prove2me | Theorems.Thm_frequently_iff_strict_mono
-- name    : frequently_iff_strict_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:49.956273+00:00
-- url     : https://prove2.me/theorems/3cb582a3-6934-4ef0-92a1-082784de9ebb
-- title:
--   frequently iff strict mono: frequently iff strict mono
-- statement:
--   An alternative characterization of "infinitely often".
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L28-L39
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L28-L39

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem frequently_iff_strict_mono {p : Stream' Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∃ φ : Stream' ℕ, StrictMono φ ∧ ∀ m, p (φ m) := by sorry
