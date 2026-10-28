-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_for_edge_count_91679e32
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_count_91679e32
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:07:45.86843+00:00
-- url     : https://prove2.me/theorems/a063f601-79c6-4628-9c39-ccf8c82521a5
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal by inclusion among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_for_edge_count_91679e32
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by sorry
