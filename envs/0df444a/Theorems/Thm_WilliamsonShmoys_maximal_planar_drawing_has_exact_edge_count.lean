-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:29:53.948268+00:00
-- url     : https://prove2.me/theorems/57594b84-ef2f-4487-b859-b2a4dc5648c7
-- title:
--   An inclusion-maximal planar graph has the triangulation edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable simple supergraph on the same vertices, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet →
      HasPlanarDrawingOn G →
      G.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
