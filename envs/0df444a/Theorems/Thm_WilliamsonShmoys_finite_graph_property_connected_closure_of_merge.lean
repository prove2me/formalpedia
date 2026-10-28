-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_connected_closure_of_merge
-- name    : WilliamsonShmoys.finite_graph_property_connected_closure_of_merge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:17:38.398566+00:00
-- url     : https://prove2.me/theorems/241d07fe-f626-45d0-ba42-03bd5c2915fd
-- title:
--   Iterating component merges for a finite graph property
-- statement:
--   If a property of finite graphs can be preserved while adding an edge that joins two distinct connected components whenever the graph is disconnected, then every disconnected graph with that property has a connected strict supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_property_connected_closure_of_merge
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K < L ∧ P L ∧ ∃ u v : V, ¬ K.Reachable u v ∧ L.Adj u v)
    (G : SimpleGraph V)
    (hG : P G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ H.Connected ∧ P H := by sorry
