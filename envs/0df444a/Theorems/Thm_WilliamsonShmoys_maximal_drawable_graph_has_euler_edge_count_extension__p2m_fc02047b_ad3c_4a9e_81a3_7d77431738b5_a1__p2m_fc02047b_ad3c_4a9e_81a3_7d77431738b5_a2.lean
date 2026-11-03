-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:49.258413+00:00
-- url     : https://prove2.me/theorems/c985394f-ff9a-4827-826c-d7a45e5d518a
-- title:
--   Triangulated edge-count completion for a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn G) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    exists N : SimpleGraph V,
      (forall u v, G.Adj u v -> N.Adj u v) /\
      HasPlanarDrawingOn N /\
      3 * Fintype.card V - 6 = N.edgeFinset.card := by sorry
