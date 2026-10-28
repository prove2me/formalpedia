-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_e2343c2d
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_e2343c2d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:02:31.366982+00:00
-- url     : https://prove2.me/theorems/a8d9336d-4b19-4375-bafa-a6e2f856d260
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs, with at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_e2343c2d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → K ≠ N → ¬ HasPlanarDrawingOn K := by sorry
