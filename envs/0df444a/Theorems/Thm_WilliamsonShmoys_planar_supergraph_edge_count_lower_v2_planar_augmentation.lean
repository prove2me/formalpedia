-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_planar_augmentation
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_planar_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:44:40.43671+00:00
-- url     : https://prove2.me/theorems/d76eaddf-fceb-41da-8ec8-d8b83385bf92
-- title:
--   A drawable graph extends to a planar graph with at least 3n−6 edges
-- statement:
--   For any graph with a crossing-free drawing on a finite ordered vertex set of size at least three, there is a crossing-free supergraph on the same vertices with at least 3|V|−6 edges. The proof route is to augment the drawing to a triangulation and use Euler's formula. The child removes the geometric augmentation and edge-count argument from the parent; the parent uses maximality to identify the supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_planar_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M ≤ N ∧
      3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by sorry
