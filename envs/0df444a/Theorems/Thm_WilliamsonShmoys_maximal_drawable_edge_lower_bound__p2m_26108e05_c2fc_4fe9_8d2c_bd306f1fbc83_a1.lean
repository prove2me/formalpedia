-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:32:50.859984+00:00
-- url     : https://prove2.me/theorems/36354cce-e9f2-4cf3-abf4-0b18020ca45b
-- title:
--   Edge lower bound from drawable maximality
-- statement:
--   If a drawable graph with at least three vertices has maximum edge count among its drawable supergraphs on the same vertex type, then its edge count is at least 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_26108e05_c2fc_4fe9_8d2c_bd306f1fbc83_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
