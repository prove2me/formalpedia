-- Prove2me | Theorems.Thm_inf_occ_proj
-- name    : inf_occ_proj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:36.417776+00:00
-- url     : https://prove2.me/theorems/f47b1b2f-9d92-442a-bba8-56a0e81b5153
-- title:
--   inf occ proj: inf occ proj
-- statement:
--   Note that only the ⊇ direction needs the finiteness assumptions.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L88-L99
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/InfOcc.lean#L88-L99

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'

theorem inf_occ_proj {I : Type*} [Finite I] {X : I → Type*} [h : ∀ i, Finite (X i)] (xs : Stream' (Π i, X i)) (i : I) :
    (· i) '' (InfOcc xs) = InfOcc ((· i) ∘ xs) := by sorry
