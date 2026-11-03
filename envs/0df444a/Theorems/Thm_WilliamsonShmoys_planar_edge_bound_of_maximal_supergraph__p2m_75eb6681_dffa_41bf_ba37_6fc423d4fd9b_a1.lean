-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:13.188238+00:00
-- url     : https://prove2.me/theorems/6d91b10d-a30f-4f1a-8acb-96a7ed12e6b9
-- title:
--   Edge bound from a maximum drawable supergraph
-- statement:
--   If a drawable graph is contained in a drawable supergraph that maximizes edge count among drawable supergraphs of the original graph, then the original graph has at most 3|V|−6 edges when |V|≥3. Maximality yields the triangulation/Euler bound for the supergraph, and edge inclusion transfers the bound to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_maximal_supergraph__p2m_75eb6681_dffa_41bf_ba37_6fc423d4fd9b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V)
    (hMN : M ≤ N)
    (hNdraw : HasPlanarDrawingOn N)
    (hmax : ∀ N' : SimpleGraph V, M ≤ N' → HasPlanarDrawingOn N' →
      (letI : DecidableRel N'.Adj := Classical.decRel N'.Adj
       N'.edgeFinset.card) ≤
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       N.edgeFinset.card))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
