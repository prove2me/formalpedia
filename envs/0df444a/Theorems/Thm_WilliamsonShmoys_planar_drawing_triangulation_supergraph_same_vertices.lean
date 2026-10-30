-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_same_vertices
-- name    : WilliamsonShmoys.planar_drawing_triangulation_supergraph_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:30:22.481432+00:00
-- url     : https://prove2.me/theorems/11e39700-d6db-44d6-8025-90a84f6dc502
-- title:
--   Triangulated planar supergraph on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices extends, on the same vertex type, to a drawn planar supergraph whose edge count is exactly 3|V|−6. The child explicitly includes edge-count monotonicity, which together with the exact count yields the parent inequality. The three-vertex boundary case is included. A proof route is to extend the drawing to a maximal planar graph on the same vertices, establish that its faces are triangular, and apply Euler’s formula. This removes the augmentation and planar counting argument from the parent; formalizing that argument for the supplied drawing predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_supergraph_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      X ≤ H ∧
      (X.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) ∧
      (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
