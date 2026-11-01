-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2
-- name    : WilliamsonShmoys.planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:36.706825+00:00
-- url     : https://prove2.me/theorems/202bf50d-736f-4a11-9464-01f4251d3269
-- title:
--   Exact edge count for a planar completion
-- statement:
--   Any finite simply drawable graph on at least three vertices can be augmented on the same vertex set to a drawable graph with exactly 3|V|−6 edges, retaining every original edge. The cardinality inequality records the monotonicity needed by the parent proof. A proof route is to add drawable edges until the graph is maximal, then use the planar maximality argument, Euler’s formula, and face-boundary counting; the vertex-count hypothesis includes the three-vertex boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
