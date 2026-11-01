-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- name    : WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:01.018104+00:00
-- url     : https://prove2.me/theorems/4344ea89-6f5a-4717-bdab-0b5d693cf9ed
-- title:
--   Exact edge count for a maximal planar graph
-- statement:
--   A finite adjacency-maximal graph with the supplied crossing-free drawing and at least three vertices has exactly `3|V| - 6` edges. The standard proof shows maximality forces a triangulation and then applies Euler's formula; the condition on the number of vertices includes the three-vertex triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd16beb0_3303_4ae5_9997_6d1ead4b529d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      (∀ u v, M.Adj u v → N.Adj u v) → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
