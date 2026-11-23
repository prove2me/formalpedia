-- Prove2me | Theorems.Thm_inf_graph_ramsey
-- name    : inf_graph_ramsey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:09:13.429935+00:00
-- url     : https://prove2.me/theorems/a256dc23-cb8f-43ac-a180-6dce86a9ebbe
-- title:
--   inf graph ramsey: inf graph ramsey
-- statement:
--   If the 2-edges of an infinite complete graph is assigned a finite number of colors,
--   then there must exist a color `c` and an infinite set `s` of vertices such that the 2-edge
--   beteen any 2 vertices of `s` is assigned the color `c`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L98-L129
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean#L98-L129

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

theorem inf_graph_ramsey :
    ∃ c : Color, ∃ s : Set Vertex, s.Infinite ∧ ∀ e : Edge (Vertex := Vertex), e.card = 2 → (e : Set Vertex) ⊆ s → color e = c := by sorry
