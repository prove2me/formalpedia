-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation__p2m_db324782_c561_499c_9a61_9d772f4e7760_a11
-- name    : WilliamsonShmoys.planar_one_edge_augmentation__p2m_db324782_c561_499c_9a61_9d772f4e7760_a11
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T04:36:25.197978+00:00
-- url     : https://prove2.me/theorems/d2a2ce8f-c512-4734-856c-7e0a6b13c160
-- title:
--   Add an edge between components of a planar drawing with at least three vertices
-- statement:
--   Every disconnected graph on a finite linearly ordered vertex type with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices that contains its edges and has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_one_edge_augmentation__p2m_db324782_c561_499c_9a61_9d772f4e7760_a11
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard < N.edgeSet.ncard := by
  sorry
