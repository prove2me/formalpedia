-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:02:26.084991+00:00
-- url     : https://prove2.me/theorems/97e2a771-8b9b-4035-b979-2c6a9ee02dac
-- title:
--   Maximal planar simple graph edge lower bound
-- statement:
--   If a drawable simple graph on at least three vertices has no drawable supergraph on the same vertex type except itself, then it has at least 3|V|−6 edges, expressed as 3|V| ≤ |E|+6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_9e9ddd37_2fbe_4f2e_b4a6_63a4b0058d20_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
