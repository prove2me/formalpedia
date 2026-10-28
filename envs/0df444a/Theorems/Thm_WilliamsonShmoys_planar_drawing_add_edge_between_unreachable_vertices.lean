-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable_vertices
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:00:44.167192+00:00
-- url     : https://prove2.me/theorems/a1be63b9-7cd4-43fe-b6cd-f30cd4fd4a96
-- title:
--   Join two components of a planar drawing by an edge
-- statement:
--   Given a planar drawing of a finite graph and two vertices that are not reachable from one another, there is a strict drawable supergraph on the same vertices. This isolates the component-joining step; its proof must redraw the components and construct a crossing-free connecting arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (u v : V)
    (hUnreachable : ¬ H.Reachable u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ HasPlanarDrawingOn K := by sorry
