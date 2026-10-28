-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_triangulated_edge_count
-- name    : WilliamsonShmoys.maximal_drawing_has_triangulated_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:43:50.887135+00:00
-- url     : https://prove2.me/theorems/981f13e1-61c3-408a-b657-d4c8e5df3a05
-- title:
--   Edge count of a maximal drawing
-- statement:
--   A maximal graph satisfying the given planar drawing predicate, on at least three fixed vertices, has exactly $3|V|-6$ edges. This removes the planar counting obligation from the parent. A proof route is to show maximality forces connectedness and triangular faces, then apply Euler’s formula and count edge-face incidences; the three-vertex case is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_has_triangulated_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K = H) :
    (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  sorry
