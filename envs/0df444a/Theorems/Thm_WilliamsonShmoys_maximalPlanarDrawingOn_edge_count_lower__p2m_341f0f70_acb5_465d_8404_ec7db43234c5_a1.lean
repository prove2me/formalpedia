-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_lower__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:22.657022+00:00
-- url     : https://prove2.me/theorems/a99e6f05-4fa1-47c0-bf14-3e0001f34ab0
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   A maximal drawable graph on at least three finite ordered vertices has at least 3|V|−6 edges. Maximality is with respect to drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_lower__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by sorry
