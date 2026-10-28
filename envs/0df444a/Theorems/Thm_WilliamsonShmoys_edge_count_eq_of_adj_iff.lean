-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_adj_iff
-- name    : WilliamsonShmoys.edge_count_eq_of_adj_iff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:41:47.446445+00:00
-- url     : https://prove2.me/theorems/8a8028e5-04cf-4c03-9fdb-34ce5bfaf6c9
-- title:
--   Adjacency equivalence identifies finite simple graphs
-- statement:
--   Two simple graphs on the same vertex type are equal when their adjacency relations agree for every pair of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_eq_of_adj_iff
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hAdj : ∀ u v, G.Adj u v ↔ K.Adj u v) :
    G = K := by sorry
