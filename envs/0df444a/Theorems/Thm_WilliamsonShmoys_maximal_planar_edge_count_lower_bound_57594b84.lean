-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_57594b84
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_57594b84
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:57:31.669098+00:00
-- url     : https://prove2.me/theorems/5685a8d2-5fbe-4329-8796-17d91f38f0d8
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at least 3n−6 edges. This isolates the triangulation consequence of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_57594b84
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet →
      HasPlanarDrawingOn G →
      G.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
