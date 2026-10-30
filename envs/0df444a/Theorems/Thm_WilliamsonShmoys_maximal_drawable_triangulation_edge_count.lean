-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:44:26.550188+00:00
-- url     : https://prove2.me/theorems/a549787b-27c9-4464-aa0b-4803a7aff3d9
-- title:
--   Edge count of maximal drawable graphs
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. Maximality rules out any nontriangular face that admits a noncrossing added edge; the triangular-face count and Euler’s formula yield the result, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
