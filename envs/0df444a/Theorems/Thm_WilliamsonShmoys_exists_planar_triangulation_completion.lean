-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_completion
-- name    : WilliamsonShmoys.exists_planar_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:00:25.290609+00:00
-- url     : https://prove2.me/theorems/ca5dbf3e-f145-4535-be74-caa3f748ef80
-- title:
--   Planar triangulation completion on the same vertices
-- statement:
--   Every connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six. This packages planar completion and the Euler count into the structural step used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
        G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
