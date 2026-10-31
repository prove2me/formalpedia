-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:08.882806+00:00
-- url     : https://prove2.me/theorems/fd86759a-355a-4193-a23e-380650ce92a8
-- title:
--   Edge bound for a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
