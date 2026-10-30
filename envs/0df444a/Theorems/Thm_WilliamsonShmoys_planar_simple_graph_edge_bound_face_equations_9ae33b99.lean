-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_face_equations_9ae33b99
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_face_equations_9ae33b99
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:43:11.468922+00:00
-- url     : https://prove2.me/theorems/48be67fb-0f86-4b93-9fbc-8fb4d3b65e22
-- title:
--   Planar simple graph edge upper bound for face equations
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This supplies the upper bound; a proof route is Euler’s formula and edge-face incidence counting, including the disconnected and bridge cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_face_equations_9ae33b99
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
