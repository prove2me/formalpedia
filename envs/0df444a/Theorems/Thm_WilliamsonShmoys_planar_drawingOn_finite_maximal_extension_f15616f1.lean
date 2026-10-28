-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_finite_maximal_extension_f15616f1
-- name    : WilliamsonShmoys.planar_drawingOn_finite_maximal_extension_f15616f1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:56:20.532994+00:00
-- url     : https://prove2.me/theorems/f3fdd4b4-363f-4836-a4ee-d9c1fc2d35a0
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every finite drawable simple graph has an inclusion-maximal drawable supergraph on the same vertex type. The class is nonempty because it contains the given graph, and there are only finitely many simple graphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_finite_maximal_extension_f15616f1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn J →
        H ≤ J → H = J := by sorry
