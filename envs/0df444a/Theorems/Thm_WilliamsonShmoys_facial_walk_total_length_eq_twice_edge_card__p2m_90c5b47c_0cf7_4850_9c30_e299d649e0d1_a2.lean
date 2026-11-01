-- Prove2me | Theorems.Thm_WilliamsonShmoys_facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- name    : WilliamsonShmoys.facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:44.97073+00:00
-- url     : https://prove2.me/theorems/4681081b-bae6-43e1-87eb-e81d14581fd2
-- title:
--   Count facial incidences as twice the edge count
-- statement:
--   If every ordered pair occurs in the flattened list exactly when it is an oriented adjacency, and then exactly once, the list length is twice the number of undirected edges. A proof sums list counts over the finite product of vertices and identifies the two orientations of each simple edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.facial_walk_total_length_eq_twice_edge_card__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (dG : DecidableRel G.Adj) (k : ℕ) (faces : Fin k → List (V × V)) (hcount : (letI : DecidableRel G.Adj := dG; ∀ u v, (List.flatten (List.ofFn faces)).count (u, v) = if G.Adj u v then 1 else 0)) : (List.flatten (List.ofFn faces)).length = 2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by sorry
