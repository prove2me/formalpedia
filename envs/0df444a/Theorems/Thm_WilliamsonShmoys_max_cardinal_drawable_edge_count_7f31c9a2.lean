-- Prove2me | Theorems.Thm_WilliamsonShmoys_max_cardinal_drawable_edge_count_7f31c9a2
-- name    : WilliamsonShmoys.max_cardinal_drawable_edge_count_7f31c9a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:29:33.28086+00:00
-- url     : https://prove2.me/theorems/40ad5c02-4cfe-4ee0-9841-6782479b4d6d
-- title:
--   Edge count of a maximum drawable supergraph
-- statement:
--   A drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges if no drawable supergraph on those vertices has more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.max_cardinal_drawable_edge_count_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet →
      HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ K.edgeSet.ncard)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
