-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:17:05.010305+00:00
-- url     : https://prove2.me/theorems/55e40668-6c6c-445f-853d-a7074df51c4e
-- title:
--   Completion of a planar drawing to triangulation edge count
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a planar supergraph on that same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
