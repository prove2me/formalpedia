-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_triangulation_extension
-- name    : WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:27:46.311362+00:00
-- url     : https://prove2.me/theorems/5a1f2bf7-5536-4d78-9659-08409f7b098c
-- title:
--   Drawable graphs extend to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly three times the number of vertices minus six edges. The supergraph need not preserve the original drawing; it must admit some planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, K ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
