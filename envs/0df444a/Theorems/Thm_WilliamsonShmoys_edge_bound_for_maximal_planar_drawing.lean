-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_for_maximal_planar_drawing
-- name    : WilliamsonShmoys.edge_bound_for_maximal_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:38:55.417707+00:00
-- url     : https://prove2.me/theorems/a7343f26-3b41-4ce4-b028-9c7717c085a3
-- title:
--   Edge bound for a maximal planar drawing
-- statement:
--   A planar simple graph on at least three vertices that is maximal by edge count among its planar supergraphs on the same vertex type satisfies the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_for_maximal_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax :
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard <= H.edgeSet.ncard) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
