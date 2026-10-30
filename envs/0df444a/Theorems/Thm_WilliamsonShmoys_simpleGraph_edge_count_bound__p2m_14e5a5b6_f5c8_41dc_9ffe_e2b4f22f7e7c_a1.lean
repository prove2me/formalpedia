-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- name    : WilliamsonShmoys.simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:36.420026+00:00
-- url     : https://prove2.me/theorems/89ba578d-aea1-42c8-b7df-4b340fede2a9
-- title:
--   Finite simple graph edge count bound
-- statement:
--   A simple graph on a finite ordered vertex type has at most the number of unordered pairs of distinct vertices as edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.simpleGraph_edge_count_bound__p2m_14e5a5b6_f5c8_41dc_9ffe_e2b4f22f7e7c_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : G.edgeSet.ncard ≤ Nat.choose (Fintype.card V) 2 := by sorry
