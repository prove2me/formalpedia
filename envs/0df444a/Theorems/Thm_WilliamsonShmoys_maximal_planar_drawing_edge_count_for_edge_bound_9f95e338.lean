-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_bound_9f95e338
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_9f95e338
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:36:22.21984+00:00
-- url     : https://prove2.me/theorems/68000e25-b98e-4b1b-b195-53b38febbbe2
-- title:
--   Count the edges of a maximal planar drawing
-- statement:
--   A graph on at least three vertices that is maximal among the planar-drawable supergraphs on that vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_9f95e338
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
