-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_graph_edge_upper_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_simple_graph_edge_upper_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:48:14.06799+00:00
-- url     : https://prove2.me/theorems/cd6d0cf9-a2ed-440c-ba5b-b1c82ce9843f
-- title:
--   Edge upper bound for a graph with a planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This separates the universal planar edge bound from the maximality argument; the proof route uses planar embedding and Euler’s formula, including disconnected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_simple_graph_edge_upper_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    W.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
