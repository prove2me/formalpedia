-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:47:03.49978+00:00
-- url     : https://prove2.me/theorems/03d955e9-c2fd-4adc-a21b-8bbb57908c10
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph has exactly 3|V|−6 edges. In a plane embedding, maximality forces connectedness and triangular faces; Euler’s formula and the count of face-edge incidences then give the stated edge count. The hypothesis |V|≥3 is needed for this formula and its triangulation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
