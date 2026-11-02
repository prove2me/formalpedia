-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:28:30.680566+00:00
-- url     : https://prove2.me/theorems/8335b04f-4e67-4cd5-9960-e59cc2d55a11
-- title:
--   An edge-maximal planar supergraph is connected
-- statement:
--   If a planar supergraph maximizes edge count among planar supergraphs of a given graph on the same finite vertex type, it is connected. The topological proof adds a planar edge between components if it is disconnected, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_supergraph_connected__p2m_03cdb16c_d4b2_4cf3_b4f1_33da613ee6f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M) (hMN : M ≤ N)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K →
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel N.Adj := Classical.decRel N.Adj
       K.edgeFinset.card ≤ N.edgeFinset.card)) :
    N.Connected := by sorry
