-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:48:32.769493+00:00
-- url     : https://prove2.me/theorems/e951fa7c-3e6e-4109-8011-74ed7e6927fa
-- title:
--   Edge lower bound forced by maximality
-- statement:
--   A graph with a crossing-free drawing that is maximal under planar edge extension, on at least three vertices, has at least 3|V|−6 edges. The proof route is to use maximality to rule out a face with a drawable missing diagonal, establish triangulation, and apply Euler’s formula. This isolates the main topological obligation while preserving all quantitative and maximality hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ X : SimpleGraph V,
      LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W) :
    3 * Fintype.card V - 6 <= W.edgeSet.ncard := by sorry
