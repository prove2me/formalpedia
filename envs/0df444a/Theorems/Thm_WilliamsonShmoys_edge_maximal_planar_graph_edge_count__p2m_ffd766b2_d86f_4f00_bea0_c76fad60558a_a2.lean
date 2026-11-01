-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:59.117536+00:00
-- url     : https://prove2.me/theorems/401bb865-eb7f-4687-8488-019108bab1f9
-- title:
--   Edge count of an edge maximal planar graph
-- statement:
--   A maximal planar simple graph with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      (∀ u v, N.Adj u v → P.Adj u v) → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
