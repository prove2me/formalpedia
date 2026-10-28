-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_euler_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:54:53.811874+00:00
-- url     : https://prove2.me/theorems/2d70374a-d6ee-453d-a765-ec58ba2081d3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same finite vertex type has exactly `3|V| − 6` edges when there are at least three vertices. The size hypothesis includes the three-vertex boundary case and is needed for the formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_euler_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T <= U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U <= T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
