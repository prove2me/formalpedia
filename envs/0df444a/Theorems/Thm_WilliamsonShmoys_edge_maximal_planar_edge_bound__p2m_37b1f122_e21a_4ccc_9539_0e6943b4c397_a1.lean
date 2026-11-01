-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:21.476767+00:00
-- url     : https://prove2.me/theorems/8d49dd8d-df70-44ed-9374-0df305c3481e
-- title:
--   Edge bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges, expressed without truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_edge_bound__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := Classical.decRel T.Adj
    3 * Fintype.card V ≤ T.edgeFinset.card + 6 := by sorry
