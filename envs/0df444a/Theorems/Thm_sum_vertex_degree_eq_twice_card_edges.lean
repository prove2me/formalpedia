-- Prove2me | Theorems.Thm_sum_vertex_degree_eq_twice_card_edges
-- name    : sum_vertex_degree_eq_twice_card_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:43:54.445638+00:00
-- url     : https://prove2.me/theorems/3758a007-e2c8-4852-9858-93444ca79225
-- title:
--   sum vertex degree eq twice card edges: sum vertex degree eq twice card edges
-- statement:
--   **Handshaking theorem:** In a loopless multigraph $G$,
--   the sum of the degrees of all vertices is twice the number of edges:
--
--   $$
--   \sum_{v \in V(G)} \deg(v) = 2 |E(G)|.
--   $$
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1733-L1744
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1733-L1744

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix

theorem sum_vertex_degree_eq_twice_card_edges (G : CFGraph) :
    ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by sorry
