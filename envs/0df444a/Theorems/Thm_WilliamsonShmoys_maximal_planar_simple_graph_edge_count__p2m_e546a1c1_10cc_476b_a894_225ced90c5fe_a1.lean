-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:38.643436+00:00
-- url     : https://prove2.me/theorems/27a5cf8c-cedc-4abf-b82c-50a7768c797c
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal finite simple graph with a crossing-free drawing and at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
