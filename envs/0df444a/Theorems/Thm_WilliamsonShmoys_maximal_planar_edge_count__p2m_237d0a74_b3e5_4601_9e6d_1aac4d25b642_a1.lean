-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:58.415035+00:00
-- url     : https://prove2.me/theorems/c8bd0d06-bddd-4d97-9a5a-50d50f58bad7
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices whose edge count is maximal among its planar supergraphs on the same vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_237d0a74_b3e5_4601_9e6d_1aac4d25b642_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
