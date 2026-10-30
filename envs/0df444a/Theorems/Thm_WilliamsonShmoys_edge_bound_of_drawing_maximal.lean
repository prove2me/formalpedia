-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_drawing_maximal
-- name    : WilliamsonShmoys.edge_bound_of_drawing_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:43:36.884978+00:00
-- url     : https://prove2.me/theorems/89675acb-5c2f-416c-b0d9-ec0234d14a08
-- title:
--   An inclusion-maximal planar drawing meets the triangulation edge bound
-- statement:
--   For a finite simple graph on at least three vertices, if it has a crossing-free drawing and every crossing-free supergraph on the same vertices has the same edge set, then its edge count plus six is at least three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_of_drawing_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S →
      G.edgeSet ⊆ S.edgeSet →
      G.edgeSet = S.edgeSet) :
    G.edgeSet.ncard + 6 >= 3 * Fintype.card V := by sorry
