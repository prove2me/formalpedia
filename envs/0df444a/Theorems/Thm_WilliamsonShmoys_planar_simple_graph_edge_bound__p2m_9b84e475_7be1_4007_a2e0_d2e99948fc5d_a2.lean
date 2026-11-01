-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:08:07.719838+00:00
-- url     : https://prove2.me/theorems/c24261b1-eccd-4339-a0db-50a7175ab071
-- title:
--   Edge bound for a drawn simple graph
-- statement:
--   Any finite simple graph on at least three vertices with a crossing-free drawing of the specified kind has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_9b84e475_7be1_4007_a2e0_d2e99948fc5d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (dG : DecidableRel G.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG;
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
