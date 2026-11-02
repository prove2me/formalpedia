-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:24:46.739436+00:00
-- url     : https://prove2.me/theorems/153db995-4c29-4000-a471-dae535324127
-- title:
--   Drawable supergraph with the planar edge lower bound
-- statement:
--   Every finite drawable simple graph on at least three vertices extends on the same vertex set to a drawable supergraph with at least 3|V| − 6 edges. This child removes the drawing-extension and edge-count argument from the parent. A proof route is to select an inclusion-maximal drawable supergraph among the finitely many graphs on V, then establish the planar edge bound using the embedding’s faces and Euler’s formula. The case |V| = 3 is included. The remaining core obligation is proving this result for the exact `HasPlanarDrawingOn` definition, including its edge-arc and crossing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V, H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V <= K.edgeFinset.card + 6) := by sorry
