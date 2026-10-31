-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:50.219733+00:00
-- url     : https://prove2.me/theorems/152d6993-7004-4697-ab26-f8c2f883dc25
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An edge-maximal drawable simple graph with at least three vertices has exactly 3n−6 edges. The proof route is to establish that maximality makes every face triangular, then use Euler’s formula and count edge-face incidences, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ S : SimpleGraph V, M ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
