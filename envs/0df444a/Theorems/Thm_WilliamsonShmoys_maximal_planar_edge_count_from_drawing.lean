-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_drawing
-- name    : WilliamsonShmoys.maximal_planar_edge_count_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:14:27.745715+00:00
-- url     : https://prove2.me/theorems/acab26a7-1987-4083-b118-5f4954238197
-- title:
--   Edge count of a maximal planar graph from its drawing
-- statement:
--   A graph on at least three vertices with a planar drawing and no proper planar supergraph on the same vertices has exactly $3n-6$ edges. The argument must show that maximality forces triangular faces and then use Euler’s formula; at three vertices the maximal graph is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_from_drawing {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
