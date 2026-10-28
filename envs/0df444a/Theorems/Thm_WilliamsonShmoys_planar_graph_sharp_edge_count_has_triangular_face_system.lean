-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_sharp_edge_count_has_triangular_face_system
-- name    : WilliamsonShmoys.planar_graph_sharp_edge_count_has_triangular_face_system
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:25:49.392166+00:00
-- url     : https://prove2.me/theorems/f423041e-5cc0-48ac-83e8-8284e4d526e4
-- title:
--   Sharp planar edge count gives triangular face system
-- statement:
--   A finite simple graph on at least three vertices with a planar drawing and exactly 3n−6 edges has a multiset of triangular faces in which each edge occurs in exactly two faces and the Euler equation holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.planar_graph_sharp_edge_count_has_triangular_face_system
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hedge : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by sorry
