-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_of_edge_count_for_triangulated_planar_data
-- name    : WilliamsonShmoys.face_data_of_edge_count_for_triangulated_planar_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:46:17.183698+00:00
-- url     : https://prove2.me/theorems/ce8a08d2-2b2f-4933-8345-649f6c0e3dc8
-- title:
--   Construct abstract triangular face data from the extremal edge count
-- statement:
--   For a finite graph on at least three vertices whose edge-set cardinality is 3n−6, there is finite abstract face data with Euler's equation, three incident edges at each face, and two incident faces at each edge. The face data need not represent a drawing of the graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData

set_option autoImplicit false

theorem WilliamsonShmoys.face_data_of_edge_count_for_triangulated_planar_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hE : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarFaceData H) := by sorry
