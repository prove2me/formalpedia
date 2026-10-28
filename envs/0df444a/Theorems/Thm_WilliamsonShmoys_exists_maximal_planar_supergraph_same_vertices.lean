-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:05:16.223316+00:00
-- url     : https://prove2.me/theorems/64e5f64b-71b0-4965-a43d-126ee256fe9f
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
