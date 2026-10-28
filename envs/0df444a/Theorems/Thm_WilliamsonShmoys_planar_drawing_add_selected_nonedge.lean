-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_selected_nonedge
-- name    : WilliamsonShmoys.planar_drawing_add_selected_nonedge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:43:13.576359+00:00
-- url     : https://prove2.me/theorems/6aea1dc7-b547-475a-9cf3-9fb65becab97
-- title:
--   Add a selected nonedge while preserving a planar drawing
-- statement:
--   Given a crossing-free drawing and a selected pair of distinct nonadjacent vertices, extend the graph on the same vertices so that it contains their edge, has strictly more edges, and still has a crossing-free drawing. The proof must construct the drawing of the extension under the predicate's exact arc conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_selected_nonedge
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (u v : V)
    (huv : u ≠ v)
    (hnot : ¬ X.Adj u v) :
    ∃ Z : SimpleGraph V,
      X ≤ Z ∧
      X.edgeSet.ncard < Z.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      Z.Adj u v := by sorry
