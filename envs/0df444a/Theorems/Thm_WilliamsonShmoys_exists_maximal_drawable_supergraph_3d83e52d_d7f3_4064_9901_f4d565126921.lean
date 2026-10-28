-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:02:27.430703+00:00
-- url     : https://prove2.me/theorems/ed29d327-8fd1-4ee9-81dd-c8434b605e76
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs under graph inclusion. Prove it by choosing a drawable supergraph with the largest edge count; there are finitely many graphs on V, and a proper supergraph has more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_3d83e52d_d7f3_4064_9901_f4d565126921
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y →
        WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X := by
  sorry
