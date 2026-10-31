-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:05.24829+00:00
-- url     : https://prove2.me/theorems/ec6e17da-f4f8-4b4d-9b03-c6a0a660eda4
-- title:
--   Planar triangulation completion and edge count
-- statement:
--   Every finite planar simple graph with at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. Extend the drawing by noncrossing diagonals until all faces are triangles, then apply Euler's formula and count face-edge incidences. At |V| = 3, the completion is the triangle. This removes the geometric completion and Euler-counting work from the parent; those are the remaining core obligations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_40d66966_5ea4_40f0_a08a_acc21533796c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ J : SimpleGraph V, H <= J ∧ HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
