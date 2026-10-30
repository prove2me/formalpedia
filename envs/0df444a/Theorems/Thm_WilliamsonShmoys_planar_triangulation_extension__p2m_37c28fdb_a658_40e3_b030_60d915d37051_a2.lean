-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:32:44.606298+00:00
-- url     : https://prove2.me/theorems/04c2f104-e4e1-4da1-bff1-5e666d9628dd
-- title:
--   Planar completion with a lower edge-count bound
-- statement:
--   Any drawable simple graph on the same finite ordered vertex type with at least three vertices has a drawable supergraph with at least 3n−6 edges. A proof route is to choose an inclusion-maximal drawable supergraph among the finitely many graphs on the vertex type, show its embedding is triangulated, and apply Euler’s formula. At n=3, maximality gives the triangle. This is the main completion argument used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      Set.Subset G.edgeSet H.edgeSet /\
      3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
