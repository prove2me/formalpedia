-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeCount
-- name    : WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeCount
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:42:56.112789+00:00
-- url     : https://prove2.me/theorems/b481bed5-ada8-42d0-8959-ea426f80fe65
-- title:
--   Edge count of an inclusion maximal planar drawing
-- statement:
--   An inclusion maximal graph with a planar drawing on at least three vertices has exactly 3n−6 edges. This child isolates the topological and counting argument: maximality forces the planar embedding to be triangulated, after which Euler’s formula and face-edge incidence counting yield the edge count. The lower bound of three vertices is retained; no separate connectedness assumption is needed for a maximal planar graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeCount
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry
