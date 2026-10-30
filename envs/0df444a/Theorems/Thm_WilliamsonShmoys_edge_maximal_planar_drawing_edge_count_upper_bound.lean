-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_upper_bound
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:12:55.901988+00:00
-- url     : https://prove2.me/theorems/900cbeb4-89ba-4e26-982f-44f7f0d97a53
-- title:
--   Upper edge count bound for a finite planar drawing
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
