-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_triangulated_euler_certificate
-- name    : WilliamsonShmoys.maximal_drawable_has_triangulated_euler_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:58:55.844612+00:00
-- url     : https://prove2.me/theorems/fa52ec1b-cf83-475c-9ef9-c5311e8a7bdd
-- title:
--   Maximal drawable graphs have a triangular Euler certificate
-- statement:
--   Every drawable simple graph on at least three vertices that is maximal among drawable supergraphs has a finite triangular Euler certificate. This isolates the topological work: derive a cellular embedding from the drawing, show maximality forces connectedness and triangular faces, and apply Euler’s formula. For three vertices, maximality forces all three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularEulerCertificate

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_has_triangulated_euler_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ X : SimpleGraph V,
      U ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = U) :
    WilliamsonShmoys.HasTriangularEulerCertificate U := by
  sorry
