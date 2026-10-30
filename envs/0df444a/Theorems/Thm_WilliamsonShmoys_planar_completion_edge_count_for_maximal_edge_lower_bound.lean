-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_for_maximal_edge_lower_bound
-- name    : WilliamsonShmoys.planar_completion_edge_count_for_maximal_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:09:08.210562+00:00
-- url     : https://prove2.me/theorems/1fcd1e10-6464-452c-bcb2-93996beee69f
-- title:
--   Planar completion with the Euler edge count
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar supergraph on that same vertex type whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count_for_maximal_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
