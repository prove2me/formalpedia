-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_edge_completion_v3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_edge_completion_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:50:58.655218+00:00
-- url     : https://prove2.me/theorems/a6fd57f2-4255-4fa1-adba-8da048cc907c
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_edge_completion_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      LE.le X Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V,
        LE.le Y Z →
        WilliamsonShmoys.HasPlanarDrawingOn Z →
        Z = Y := by sorry
