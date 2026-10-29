-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge
-- name    : WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:52:00.888992+00:00
-- url     : https://prove2.me/theorems/10326427-f5ce-4956-94e3-04a0599776f7
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   An inclusion maximal graph with a crossing-free drawing on at least three vertices has at least 3n−6 edges. A proof route is to extend the drawing to a triangulation without adding vertices, then apply maximality to show the extension equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
