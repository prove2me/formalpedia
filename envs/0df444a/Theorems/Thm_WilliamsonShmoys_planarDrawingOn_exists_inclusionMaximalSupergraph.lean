-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_inclusionMaximalSupergraph
-- name    : WilliamsonShmoys.planarDrawingOn_exists_inclusionMaximalSupergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:41:47.538221+00:00
-- url     : https://prove2.me/theorems/8a05a433-2e4f-414e-8cbf-765c21debd83
-- title:
--   Existence of an inclusion maximal planar supergraph
-- statement:
--   For every graph with a planar drawing on a finite ordered vertex type, there is a planar supergraph on that same type that is maximal under inclusion. Finiteness permits maximizing the edge count among the planar supergraphs of L; a planar extension of the maximizer cannot add an edge. This child removes the completion-existence step from the parent and does not require connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_exists_inclusionMaximalSupergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
