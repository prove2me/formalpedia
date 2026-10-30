-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:39:03.596173+00:00
-- url     : https://prove2.me/theorems/f4f3e817-70a1-4965-8e95-800989e69db0
-- title:
--   Triangulated planar extension
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
