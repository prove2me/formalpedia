-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:15.599628+00:00
-- url     : https://prove2.me/theorems/6a98dd8c-93db-41f3-b936-6f734f02a42e
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing on at least three vertices has at least $3|V|-6$ edges. This isolates the maximality-to-triangulation part of the source argument from the general edge upper bound. A proof route is to show maximality forces the drawing to be connected and every face to be triangular: any face with a boundary that permits a nonedge chord would allow adding that edge while preserving planarity, contradicting `hMax`. Euler's formula and counting face-edge incidences then give the inequality. This route needs the stated vertex lower bound and the full maximality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
