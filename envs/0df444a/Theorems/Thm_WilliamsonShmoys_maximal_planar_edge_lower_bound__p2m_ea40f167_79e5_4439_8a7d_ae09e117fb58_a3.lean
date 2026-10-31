-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:06.450725+00:00
-- url     : https://prove2.me/theorems/f9467e46-2ce6-4b9f-b76a-966f262664e2
-- title:
--   Edge lower bound for a maximal finite planar graph
-- statement:
--   A drawable graph maximal among drawable graphs on the same vertex type has at least 3n − 6 edges. This supplies the lower bound needed for equality in the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea40f167_79e5_4439_8a7d_ae09e117fb58_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
