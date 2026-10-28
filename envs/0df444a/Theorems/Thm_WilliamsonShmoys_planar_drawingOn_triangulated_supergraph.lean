-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_supergraph
-- name    : WilliamsonShmoys.planar_drawingOn_triangulated_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:41:42.328162+00:00
-- url     : https://prove2.me/theorems/988ff1dd-718e-4cf1-aa5e-cbe038916ed9
-- title:
--   Planar drawing has a triangulated supergraph
-- statement:
--   Complete the given crossing-free drawing to a graph on the same finite vertex type that still has such a drawing, contains every edge of `U`, and has exactly `3n − 6` edges. The statement preserves the `n ≥ 3` condition; at `n = 3`, the completion is a triangle. This isolates the topological completion and edge-count obligation needed by the parent. A proof route is to derive a plane embedding from the supplied arcs, add edges within faces to connect components and triangulate, then use Euler’s formula and face-edge incidence counting. The precise drawing definition and disconnected case are the remaining core work; related claims in the available research notes are open or disproved, so this route is not an established result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      (∀ u v, U.Adj u v → W.Adj u v) ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
