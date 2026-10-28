-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_fixed_vertices
-- name    : WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:05:35.285875+00:00
-- url     : https://prove2.me/theorems/2b2bbb5c-14de-4433-af7a-1d29c3335de9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices with no proper drawable supergraph on those vertices has exactly `3n − 6` edges. A proof route is to show maximality forces a connected triangulation and then count its edges with Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
