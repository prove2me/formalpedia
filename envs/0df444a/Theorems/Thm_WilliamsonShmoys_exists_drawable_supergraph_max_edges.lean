-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edges
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_edges
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:38:39.604896+00:00
-- url     : https://prove2.me/theorems/f15d1e15-b99d-4ac5-bae5-0d9d2779360b
-- title:
--   Drawable supergraph with maximum edge count
-- statement:
--   For a drawable graph on a finite linearly ordered vertex type, some drawable supergraph containing it has at least as many edges as every other drawable supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_max_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ M : SimpleGraph V,
      T ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, T ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
