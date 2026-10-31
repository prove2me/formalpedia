-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:00:09.078792+00:00
-- url     : https://prove2.me/theorems/7c57b747-c460-4faf-9469-5a2ac820d0a0
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A graph maximal among drawable supergraphs on the same finite ordered vertex type has exactly 3|V|−6 edges when the vertex count is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
