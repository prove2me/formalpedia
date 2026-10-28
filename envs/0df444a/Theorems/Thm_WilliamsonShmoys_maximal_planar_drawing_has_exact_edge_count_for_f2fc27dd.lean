-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:30:40.94498+00:00
-- url     : https://prove2.me/theorems/fad5e82d-4b2c-4a7e-abf6-71a91af3a271
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three finite vertices that is maximal under drawable supergraph inclusion has exactly $3|V|-6$ edges. This removes the planar-topology and Euler-count argument from the parent while preserving its exact quantitative conclusion. A proof route is to use the drawing to show maximality forces connectedness and triangular faces, and then combine Euler’s formula with the fact that each edge borders two face sides. The hypothesis of at least three vertices is needed for the triangulation edge-count formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
