-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:24:04.940418+00:00
-- url     : https://prove2.me/theorems/1095f796-c580-4096-843f-cd051f083539
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges. This removes the triangulation and Euler-counting argument from the parent. A proof route is to show maximality forces triangular faces, apply Euler's formula, and count each edge twice among face boundaries. The lower bound is needed: at three vertices the conclusion gives three edges; below three vertices it is not valid in general.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) : 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
