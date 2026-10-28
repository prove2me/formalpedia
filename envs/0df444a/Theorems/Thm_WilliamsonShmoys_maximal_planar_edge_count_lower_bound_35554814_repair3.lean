-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_35554814_repair3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_35554814_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:56:41.403615+00:00
-- url     : https://prove2.me/theorems/2f5e0f27-8b03-47f0-970e-214c2fe0bbec
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3|V| − 6` edges. Extend its planar drawing to a maximal plane graph on the same vertices; the supplied maximality forces the extension to be the original graph, so triangulation and Euler’s formula give the bound. For three vertices, maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_35554814_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      Set.Subset P.edgeSet Q.edgeSet → Set.Subset Q.edgeSet P.edgeSet) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by sorry
