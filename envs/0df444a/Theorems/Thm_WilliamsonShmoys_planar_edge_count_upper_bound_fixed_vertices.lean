-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fixed_vertices
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_fixed_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:23:17.499151+00:00
-- url     : https://prove2.me/theorems/adb299c8-4e48-42ff-8cc3-e2dc6a62d1dd
-- title:
--   Planar edge-count upper bound on fixed vertices
-- statement:
--   A drawable simple graph on at least three finite vertices has at most 3n−6 edges. The proof route is Euler’s formula and face-edge counting for the drawing; n≥3 is needed for the simple-graph face-length bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
