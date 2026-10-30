-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_lower_edge_bound_triangulated_completion_679bf6a6_fac0_4eb8_a381_2f80a1e33cc2
-- name    : WilliamsonShmoys.maximal_drawing_lower_edge_bound_triangulated_completion_679bf6a6_fac0_4eb8_a381_2f80a1e33cc2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:00:42.213059+00:00
-- url     : https://prove2.me/theorems/a3e3cf18-dbe0-4663-84f0-17bd5e59149d
-- title:
--   Triangulated completion edge count for a finite planar drawing
-- statement:
--   Every finite graph with a crossing-free drawing on a linearly ordered vertex type and at least three vertices is contained, on the same vertex set, in a drawable graph with exactly 3|V|−6 edges. At three vertices, the completion can be the triangle. The parent combines this completion with maximality to identify the original and completed edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_lower_edge_bound_triangulated_completion_679bf6a6_fac0_4eb8_a381_2f80a1e33cc2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
