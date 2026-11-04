-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- name    : WilliamsonShmoys.subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:21.239938+00:00
-- url     : https://prove2.me/theorems/0c1d2833-de32-49c5-aebf-88ae0a9260a2
-- title:
--   Subgraphs of maximal drawable graphs obey the planar edge bound
-- statement:
--   If a drawable graph on at least three vertices is maximal among drawable graphs on those vertices, every subgraph has at most three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_of_maximal_planar_drawing_obeys_edge_bound__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hsub : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  sorry
