-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_exists_maximal_supergraph
-- name    : WilliamsonShmoys.planarDrawing_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:32:48.507481+00:00
-- url     : https://prove2.me/theorems/cff59801-9b23-462e-9f4a-305fd7df916d
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph maximal under edge inclusion. The finiteness of the simple graphs on the fixed vertex type gives an independent proof by maximizing edge count; no vertex-count lower bound is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
