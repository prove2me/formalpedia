-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_connected_closure_of_merge_with_card_bound
-- name    : WilliamsonShmoys.finite_graph_property_connected_closure_of_merge_with_card_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:25:13.598052+00:00
-- url     : https://prove2.me/theorems/c24f94e3-2846-4df8-a311-18310eb2acc0
-- title:
--   Iterating component merges with a fixed size bound
-- statement:
--   For a property on graphs over a fixed finite vertex type, if every disconnected graph with at least three vertices can be enlarged while preserving the property by adding an edge between distinct components, then any such disconnected graph has a connected strict supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_property_connected_closure_of_merge_with_card_bound
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ K : SimpleGraph V, 3 ≤ Fintype.card V → P K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K < L ∧ P L ∧ ∃ u v : V, ¬ K.Reachable u v ∧ L.Adj u v)
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : P G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ H.Connected ∧ P H := by sorry
