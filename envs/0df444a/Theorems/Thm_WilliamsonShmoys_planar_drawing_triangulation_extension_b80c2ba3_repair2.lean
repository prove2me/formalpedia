-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:15:38.017352+00:00
-- url     : https://prove2.me/theorems/32f944ef-862d-44fe-b8be-1b5a52d2649b
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   Every drawable simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is 3|V|−6. A proof can augment the finite embedded graph to a triangulation and apply Euler’s formula with triangular-face incidence counting. The vertex-count hypothesis is required for this extension result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
