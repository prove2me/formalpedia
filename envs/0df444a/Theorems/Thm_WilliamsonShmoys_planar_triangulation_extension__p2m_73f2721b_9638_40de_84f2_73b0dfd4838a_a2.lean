-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:33:38.320728+00:00
-- url     : https://prove2.me/theorems/4aa408bd-17d9-4917-9c01-10ab9168a102
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn is a subgraph of a drawable simple graph on the same vertices with exactly 3|V|−6 edges. This includes disconnected input; joining components is part of the extension argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    Exists fun T : SimpleGraph V =>
      And (G.edgeSet ⊆ T.edgeSet)
        (And (HasPlanarDrawingOn T)
          (T.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  sorry
