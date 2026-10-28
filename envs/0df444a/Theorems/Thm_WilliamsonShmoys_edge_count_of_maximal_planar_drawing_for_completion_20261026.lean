-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_for_completion_20261026
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_completion_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:09:17.807825+00:00
-- url     : https://prove2.me/theorems/dc40f892-c316-4802-b550-187ffbaab99a
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   Any drawable graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex type has exactly `3 * Fintype.card V - 6` edges. The proof route is to show maximality forces a triangulation, then apply Euler’s formula and count face-edge incidences; the hypothesis `3 ≤ Fintype.card V` covers the boundary and natural subtraction. This child contains the remaining geometric and planar-counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_completion_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
