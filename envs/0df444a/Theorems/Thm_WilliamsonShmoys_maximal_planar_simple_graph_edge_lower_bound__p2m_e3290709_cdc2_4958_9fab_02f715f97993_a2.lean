-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:40.753243+00:00
-- url     : https://prove2.me/theorems/85ec4d12-af4e-4e6b-adb3-c8b105f3133d
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A graph with a planar drawing that is maximal among drawable supergraphs on the same vertex type and has at least three vertices has at least `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by sorry
