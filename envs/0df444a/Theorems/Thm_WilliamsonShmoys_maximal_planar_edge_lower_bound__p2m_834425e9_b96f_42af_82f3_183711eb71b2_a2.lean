-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:34.62044+00:00
-- url     : https://prove2.me/theorems/6a93ee10-5962-45c7-890c-230c5f08b7cb
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by sorry
