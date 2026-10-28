-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_has_triangular_faces
-- name    : WilliamsonShmoys.maximal_planar_supergraph_has_triangular_faces
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:22:51.771983+00:00
-- url     : https://prove2.me/theorems/10b1d34c-bbe0-413e-8fa8-15826519102f
-- title:
--   A maximal planar graph has a triangular plane face system
-- statement:
--   If a finite simple graph on at least three vertices admits the specified planar drawing and has no strictly larger planar supergraph on those vertices, then its plane faces form a triangular plane face system.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_has_triangular_faces
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem K := by sorry
