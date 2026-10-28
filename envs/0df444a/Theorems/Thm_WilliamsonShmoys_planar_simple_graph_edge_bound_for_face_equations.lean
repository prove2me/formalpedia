-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_face_equations
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:02:56.245995+00:00
-- url     : https://prove2.me/theorems/67227ad7-9214-4ad9-bebf-3e1ea8ac593a
-- title:
--   Simple planar graph edge bound for face equations
-- statement:
--   A graph with the supplied crossing-free drawing and at least three vertices has at most `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
