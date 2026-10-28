-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- name    : WilliamsonShmoys.edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:22:19.946785+00:00
-- url     : https://prove2.me/theorems/48eb24e9-5896-4a37-8d2b-2ca8a7797d82
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph with at least three vertices that has no proper drawable supergraph on the same vertices has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hMax : forall R : SimpleGraph V,
      (forall u v, T.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R -> R = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
