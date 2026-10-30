-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:55.411453+00:00
-- url     : https://prove2.me/theorems/caf8a86e-ba48-4365-a372-a27064dc0c60
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices whose edge count is at least that of every planar supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
