-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_graph_equiv
-- name    : WilliamsonShmoys.edge_count_eq_of_graph_equiv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:35:57.177788+00:00
-- url     : https://prove2.me/theorems/a0afe24f-7eb3-4df0-ba50-49b13682cf3a
-- title:
--   Mutual graph inclusion gives equal edge counts
-- statement:
--   If each of two finite simple graphs contains the other, their edge counts agree. Prove adjacency extensionality from the two inclusions, obtain equality of the graphs or their edge sets, and use equality to show the finite cardinalities agree. This removes the graph-order and finite-count bookkeeping from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_eq_of_graph_equiv
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L) (hLK : L ≤ K) :
    K.edgeSet.ncard = L.edgeSet.ncard := by sorry
