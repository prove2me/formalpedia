-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:31.030553+00:00
-- url     : https://prove2.me/theorems/dddaee3a-0582-44d9-9566-a5dd1d115710
-- title:
--   Connected planar supergraph with at least three vertices
-- statement:
--   For a finite ordered vertex type with at least three vertices, every graph with a crossing-free drawing has a connected drawable supergraph on the same vertices. Existing edges and vertices are preserved; the size hypothesis excludes the empty-vertex counterexample to the earlier unrestricted statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_of_three_vertices__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
