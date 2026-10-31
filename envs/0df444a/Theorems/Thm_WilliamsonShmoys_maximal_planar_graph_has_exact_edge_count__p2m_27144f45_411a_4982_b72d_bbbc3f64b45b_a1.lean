-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:36.812957+00:00
-- url     : https://prove2.me/theorems/7ed45ce9-fab7-4799-9a3a-4afc5611b50c
-- title:
--   Maximal planar graph edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
