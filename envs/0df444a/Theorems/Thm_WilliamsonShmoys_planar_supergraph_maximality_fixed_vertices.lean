-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximality_fixed_vertices
-- name    : WilliamsonShmoys.planar_supergraph_maximality_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:36:57.643989+00:00
-- url     : https://prove2.me/theorems/efea81cb-9a56-4837-84db-d90f042cf7b7
-- title:
--   Existence of a maximal planar supergraph on the fixed vertex set
-- statement:
--   Every finite graph with a crossing-free drawing has a planar supergraph on the same vertex set that is maximal among planar supergraphs on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_maximality_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) := by sorry
