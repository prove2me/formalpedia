-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_count_completion_nat
-- name    : WilliamsonShmoys.planar_drawing_has_edge_count_completion_nat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:50:36.036016+00:00
-- url     : https://prove2.me/theorems/c10b408b-b7ec-40f0-b964-0a6697295590
-- title:
--   Drawable graph completion with exact planar edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. For three vertices the completion is the triangle; in general the proof extends the drawing to a maximal planar graph and counts its triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_count_completion_nat
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
