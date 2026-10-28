-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:06:01.339004+00:00
-- url     : https://prove2.me/theorems/77688e3f-7514-42cb-a7d8-a891c0c066d0
-- title:
--   A planar drawing extends to a triangulated graph
-- statement:
--   Every finite simple graph with the specified planar drawing and at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The proof extends the drawing to a maximal planar drawing and uses Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_extension {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
