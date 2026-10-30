-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_bd88397e_retry3
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_bd88397e_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:53:04.007723+00:00
-- url     : https://prove2.me/theorems/2a3bf938-54d7-4ba6-ba97-85998ae61b74
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges, including when the graph is disconnected. This isolates the Euler and face-incidence part of the proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_bd88397e_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
