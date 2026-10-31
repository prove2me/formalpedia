-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:41.552011+00:00
-- url     : https://prove2.me/theorems/b57320a1-3d4d-47a8-9143-c11c47990f42
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices that is maximal under planar supergraph inclusion has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
