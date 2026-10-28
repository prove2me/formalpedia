-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count_20261026
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:10:41.462877+00:00
-- url     : https://prove2.me/theorems/dad7fe2d-8c9e-4217-9766-0577ae1aff58
-- title:
--   Planar completion with maximal planar edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
