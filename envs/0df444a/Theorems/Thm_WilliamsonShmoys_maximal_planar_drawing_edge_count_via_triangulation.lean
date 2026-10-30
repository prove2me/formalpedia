-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_via_triangulation
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_via_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:51:12.49863+00:00
-- url     : https://prove2.me/theorems/464955b7-2111-4129-b16c-82c63e0f267b
-- title:
--   Edge count of a maximal planar drawing via triangulation
-- statement:
--   A drawable graph on at least three finite ordered vertices that admits no drawable edge supergraph has exactly `3n - 6` edges. Show maximality forces a triangulation, handling disconnected drawings and the three-vertex boundary case, then count edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_via_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
