-- Prove2me | Theorems.Thm_option_some_pigeonhole
-- name    : option_some_pigeonhole
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:39.867298+00:00
-- url     : https://prove2.me/theorems/b07821ef-59eb-46fa-9c41-6e40c07dec9d
-- title:
--   option some pigeonhole: option some pigeonhole
-- statement:
--   The option some pigeonhole construction uses the option some pigeonhole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L185-L198
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L185-L198

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'

theorem option_some_pigeonhole {X : Type*} [Finite X] {n : ℕ} (f : Fin n → Option X)
    (h : {j | (f j).isSome}.ncard > Nat.card X) :
    ∃ j1 j2, j1 ≠ j2 ∧ ∃ x, f j1 = some x ∧ f j2 = some x := by sorry
