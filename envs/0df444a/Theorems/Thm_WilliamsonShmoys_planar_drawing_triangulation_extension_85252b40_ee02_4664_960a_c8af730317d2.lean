-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:14:57.159538+00:00
-- url     : https://prove2.me/theorems/9f85cd51-b9ae-4775-810a-d5fb5ec242df
-- title:
--   Extend a planar drawing to a triangular plane face system
-- statement:
--   A finite graph with at least three vertices and the specified crossing-free drawing has a supergraph on the same vertices that still has such a drawing and admits a triangular plane face system.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_85252b40_ee02_4664_960a_c8af730317d2
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem K := by sorry
