-- Prove2me | Theorems.Thm_selection_seq_prop
-- name    : selection_seq_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:09:13.662742+00:00
-- url     : https://prove2.me/theorems/279a1c06-0da6-4289-9e2b-4f19f829b151
-- title:
--   selection seq prop: selection seq prop
-- statement:
--   The selection seq prop construction uses the selection seq prop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L83-L92
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L83-L92

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
set_option autoImplicit true
open Function Set
open Classical
variable {Color Vertex : Type*} [Finite Color]
variable (color : (e : Edge) → Color)
variable [Infinite Vertex]

theorem selection_seq_prop :
    ∃ vs : ℕ → Set Vertex, ∃ v : ℕ → Vertex, ∃ c : ℕ → Color,
    ∀ n, vs n ⊆ (⋂ m < n, vs m) ∧ v n ∈ (⋂ m < n, vs m) \ (vs n) ∧ ∀ u ∈ vs n, color {v n, u} = c n := by sorry
