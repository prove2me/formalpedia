-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_adds_edge_between_unreachable_vertices
-- name    : WilliamsonShmoys.planar_drawing_adds_edge_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:50:22.874988+00:00
-- url     : https://prove2.me/theorems/1a309e2f-1341-456a-bab1-4766684fdf01
-- title:
--   A planar drawing can be extended by an edge between components
-- statement:
--   Given a finite ordered graph drawing and two vertices in different connected components, add an edge between them while retaining a crossing-free drawing on the same vertex type. Non-reachability ensures the vertices are distinct and the added edge was not already present. This isolates the topological work; the parent derives such a pair directly from disconnectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_adds_edge_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    {u v : V} (huv : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
