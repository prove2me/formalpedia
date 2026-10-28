-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
-- name    : WilliamsonShmoys.planar_drawingOn_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:16:35.533808+00:00
-- url     : https://prove2.me/theorems/bf1f9620-ba53-43a4-8df7-165664f1764d
-- title:
--   Planar drawing edge bound
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
