-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_lower_bound_for_maximal_exact_count
-- name    : WilliamsonShmoys.planar_augmentation_lower_bound_for_maximal_exact_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:40:32.979617+00:00
-- url     : https://prove2.me/theorems/11b3a564-6a8b-460f-9b21-ee21f3fb131d
-- title:
--   Maximal planar drawing reaches the triangulation lower bound
-- statement:
--   If a drawable graph on at least three vertices is inclusion-maximal among drawable graphs on the same vertex type, it has at least 3|V|−6 edges. A proof can augment the drawing on the same vertices to a triangulated planar supergraph, then use maximality to identify that supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_lower_bound_for_maximal_exact_count
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    3 * Fintype.card V <= J.edgeSet.ncard + 6 := by sorry
