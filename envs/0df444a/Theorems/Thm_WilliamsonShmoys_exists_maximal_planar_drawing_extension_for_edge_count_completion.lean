-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_for_edge_count_completion
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension_for_edge_count_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:45:41.060014+00:00
-- url     : https://prove2.me/theorems/a38da645-4644-4201-9c72-57ec9d1ac6d0
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension_for_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
