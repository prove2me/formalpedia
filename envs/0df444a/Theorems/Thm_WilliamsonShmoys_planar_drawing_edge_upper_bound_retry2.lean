-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_retry2
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:42:51.520395+00:00
-- url     : https://prove2.me/theorems/217ef723-d8d6-4cf8-a756-f72ae4cf0ee7
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This removes the upper-bound half of the target; a proof can convert the arc drawing to a planar embedding and use Euler’s formula, treating connected components and small components separately.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
