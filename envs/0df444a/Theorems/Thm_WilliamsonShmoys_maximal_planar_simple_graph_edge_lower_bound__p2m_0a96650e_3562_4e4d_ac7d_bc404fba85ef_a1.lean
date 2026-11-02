-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- name    : WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:41.561419+00:00
-- url     : https://prove2.me/theorems/54520c23-fb0c-40a7-a4c0-ad4b1f033824
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has at least 3|V|−6 edges. The argument extends a drawable graph to a triangulated maximal drawable supergraph on the same vertex set, then applies the given maximality hypothesis and counts incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_0a96650e_3562_4e4d_ac7d_bc404fba85ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by sorry
