-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_join_unreachable_vertices__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
-- name    : WilliamsonShmoys.planar_drawing_join_unreachable_vertices__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:09.873718+00:00
-- url     : https://prove2.me/theorems/2bf3c0fa-9c68-4a9d-aeed-15f64450a5fb
-- title:
--   Join two components of a planar drawing
-- statement:
--   Given a planar drawing of a finite graph and two distinct vertices in different connected components, there is a planar supergraph on the same vertices that contains the edge between them. This is the geometric core: redraw the finite components in separated regions, then draw a joining arc without crossings. The new edge establishes strictness because the original graph cannot contain an edge between unreachable vertices. The supplied drawing predicate's endpoint ordering can be handled by orienting the joining arc according to the vertex order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_join_unreachable_vertices__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ K.Reachable u v) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K' ≠ K ∧
      K'.Adj u v := by sorry
