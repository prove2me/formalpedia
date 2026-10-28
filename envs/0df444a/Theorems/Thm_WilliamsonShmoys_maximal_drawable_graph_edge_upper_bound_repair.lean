-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_upper_bound_repair
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_upper_bound_repair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:52:49.920592+00:00
-- url     : https://prove2.me/theorems/bdada46f-dc6d-438c-a3de-28c4e37419c4
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with the specified crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. The proof requires deriving the planar Euler and face-degree bounds from the given drawing representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_upper_bound_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
