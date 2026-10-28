-- Prove2me | Theorems.Thm_planar_drawing_has_maximal_planar_extension
-- name    : planar_drawing_has_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:07:25.213238+00:00
-- url     : https://prove2.me/theorems/e39ebbcc-21b1-4054-a0d4-61a611cb0dc0
-- title:
--   Extend a finite planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph with the supplied drawing has a drawing-preserving supergraph on the same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planar_drawing_has_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
