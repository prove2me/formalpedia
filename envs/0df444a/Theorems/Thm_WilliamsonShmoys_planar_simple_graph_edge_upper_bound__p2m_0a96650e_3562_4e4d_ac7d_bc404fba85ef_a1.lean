-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:39.788777+00:00
-- url     : https://prove2.me/theorems/25b88d59-9c9b-4413-bef8-c3d95089e4b3
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any drawable simple graph on at least three finite ordered vertices has at most 3|V|−6 edges. This is the Euler-count portion, independent of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
