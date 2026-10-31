-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:09.457412+00:00
-- url     : https://prove2.me/theorems/31727deb-1ab6-43dd-805b-f9cbe6cd890f
-- title:
--   Planar triangulation completion on a fixed vertex type
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

/-- Every drawable simple graph on at least three vertices has a drawable
supergraph on the same vertex type with the edge count of a triangulation. -/

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
    {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
