-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_from_extension_98d9ecda
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_extension_98d9ecda
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:28:31.980551+00:00
-- url     : https://prove2.me/theorems/9f8c31a1-ded7-4202-9963-82cfbd43c092
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its number of vertices minus six edges. The three-vertex boundary case gives the triangle, with three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_from_extension_98d9ecda
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hDraw : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X = W) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
