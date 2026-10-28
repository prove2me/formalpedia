-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_augmentation
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:39:14.665261+00:00
-- url     : https://prove2.me/theorems/cf3c4e45-adb8-4f7a-9575-01226c81268d
-- title:
--   Existence of a maximal planar supergraph for edge augmentation
-- statement:
--   Any graph with a planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn N) := by sorry
