-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:03.226229+00:00
-- url     : https://prove2.me/theorems/0e129449-44b7-4ec4-9782-615c2e23c561
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three finite vertices that is maximal under drawable same-vertex supergraphs has at least `3 * |V| - 6` edges, expressed without truncated subtraction. A proof route is to extend the graph to a triangulation on the same vertex set; maximality makes the extension equal to the original graph, and Euler’s formula gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M)
    : letI : DecidableRel M.Adj := dM
      6 * Fintype.card V ≤ 2 * M.edgeFinset.card + 12 := by sorry
