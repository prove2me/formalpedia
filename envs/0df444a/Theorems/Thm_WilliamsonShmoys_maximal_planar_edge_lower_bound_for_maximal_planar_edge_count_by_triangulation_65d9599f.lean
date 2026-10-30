-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:36:59.898441+00:00
-- url     : https://prove2.me/theorems/63d03fb4-4127-47b2-acd2-43e358f77e1a
-- title:
--   Maximality gives the planar triangulation lower bound
-- statement:
--   An inclusion-maximal finite simple graph admitting the supplied planar drawing, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
