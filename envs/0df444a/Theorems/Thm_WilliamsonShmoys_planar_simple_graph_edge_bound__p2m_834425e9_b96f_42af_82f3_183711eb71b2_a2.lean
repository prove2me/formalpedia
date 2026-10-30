-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:32.959263+00:00
-- url     : https://prove2.me/theorems/d908ff8e-b2ea-4f26-9ee5-97f35f4c9df1
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
