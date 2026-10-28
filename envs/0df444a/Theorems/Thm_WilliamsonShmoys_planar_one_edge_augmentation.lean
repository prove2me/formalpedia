-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation
-- name    : WilliamsonShmoys.planar_one_edge_augmentation
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T22:28:04.241486+00:00
-- url     : https://prove2.me/theorems/7c7a6b3e-dad2-4213-ba25-da2e9acc18b7
-- title:
--   Add an edge between components of a planar drawing
-- statement:
--   Every disconnected graph with a crossing-free drawing on a finite ordered vertex type has a planar supergraph on the same vertices with strictly more edges. The strict increase ensures that each application makes progress; the argument must preserve the exact drawing conditions in `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_one_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdisc : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard < N.edgeSet.ncard := by
  sorry
