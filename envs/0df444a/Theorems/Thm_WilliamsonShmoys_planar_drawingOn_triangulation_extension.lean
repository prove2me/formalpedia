-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:00:55.978951+00:00
-- url     : https://prove2.me/theorems/96bc7f97-7b3d-41f0-b175-8998606a0e55
-- title:
--   Planar drawing extends to a triangulation on the same vertices
-- statement:
--   Every simple graph with a crossing-free drawing on at least three vertices extends, without adding vertices, to a drawable triangulated graph with exactly 3|V|−6 edges. The parent applies maximality to force this extension to have the same edge set as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
