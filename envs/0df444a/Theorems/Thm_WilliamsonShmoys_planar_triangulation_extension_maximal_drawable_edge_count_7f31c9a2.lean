-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_drawable_edge_count_7f31c9a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_edge_count_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:47:59.580987+00:00
-- url     : https://prove2.me/theorems/7c06fb87-1c2f-4e85-b3d3-17c8ce2c8782
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. For |V| = 3, maximality forces all three possible edges, so the equation holds. For larger finite vertex sets, the independent proof route is to use the supplied drawing to show maximality forces connectedness and triangular faces, then apply Euler’s formula and double-count face-edge incidences. This child carries the geometric and planar-counting core; the parent only needs to apply it to the maximal supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_edge_count_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet → HasPlanarDrawingOn J →
        J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
