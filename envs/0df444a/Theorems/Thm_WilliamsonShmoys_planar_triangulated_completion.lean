-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion
-- name    : WilliamsonShmoys.planar_triangulated_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:32:36.941217+00:00
-- url     : https://prove2.me/theorems/e69220cf-5cc1-4342-a84f-9ccd3d593737
-- title:
--   Triangulated completion of a drawable graph
-- statement:
--   Every graph drawable on a finite vertex set of size at least three has a drawable supergraph on that same vertex set whose edge count is exactly 3n−6. The hypothesis permits disconnected graphs and retains the n ≥ 3 boundary condition. Prove this by extending the drawing to a triangulation and applying Euler's formula with face-edge incidence counting. This removes the geometric completion and counting work from the parent; the parent then uses maximality to identify the completion with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
