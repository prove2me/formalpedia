-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:26.928025+00:00
-- url     : https://prove2.me/theorems/bd8d0600-4145-46ea-8bb6-b60141056e98
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable simple supergraph on the same vertices has exactly `3|V| - 6` edges. The independent proof route is to show maximality forces connectedness and triangular faces, then combine Euler's formula with the fact that each edge is incident to two face-sides. This isolates the topological edge-count argument from the parent. The lower boundary `|V| = 3` is included and yields three edges; the hypothesis `3 ≤ |V|` is needed for the maximal-planar edge-count result. This child contains the remaining core topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, HasPlanarDrawingOn J ->
      (forall u v, H.Adj u v -> J.Adj u v) ->
      (forall u v, J.Adj u v -> H.Adj u v)) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
