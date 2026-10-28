-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_of_connected_drawing
-- name    : WilliamsonShmoys.triangulated_supergraph_of_connected_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:09:38.192895+00:00
-- url     : https://prove2.me/theorems/f989d15a-9de4-46ba-a064-c857ec5b8d7e
-- title:
--   Triangulate a connected planar drawing
-- statement:
--   A connected simple planar graph on at least three vertices can be augmented on the same vertex set to a triangulated planar supergraph. Its edge count then satisfies E + 6 = 3n. The lower bound n ≥ 3 is needed for the triangulation and excludes small-vertex exceptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_supergraph_of_connected_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
