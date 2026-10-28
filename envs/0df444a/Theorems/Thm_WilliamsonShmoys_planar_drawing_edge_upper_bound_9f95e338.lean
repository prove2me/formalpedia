-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_9f95e338
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_9f95e338
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:52:38.533569+00:00
-- url     : https://prove2.me/theorems/9d11d667-44f8-403a-b06e-76ed18836ecd
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices has at most 3|V|−6 edges. This is the Euler planar edge bound; the vertex-count hypothesis covers the small-graph boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_9f95e338
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
