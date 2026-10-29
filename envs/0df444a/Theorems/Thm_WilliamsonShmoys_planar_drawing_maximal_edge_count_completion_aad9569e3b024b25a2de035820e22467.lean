-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:41:27.974413+00:00
-- url     : https://prove2.me/theorems/9b8f8c40-a15e-486b-81d1-8c0e4c9839ea
-- title:
--   Completion of a planar drawing with maximal edge count
-- statement:
--   Every graph with the specified crossing-free drawing on a finite linearly ordered vertex type of size at least three is contained in a drawable graph on the same vertex set with exactly 3n − 6 edges. For three vertices, this completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
