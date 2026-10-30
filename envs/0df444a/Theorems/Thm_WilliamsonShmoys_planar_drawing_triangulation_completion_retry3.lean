-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:33:21.051304+00:00
-- url     : https://prove2.me/theorems/fe19d700-9f28-45dd-829d-ba4f391d3236
-- title:
--   Complete a finite planar drawing to a triangulation
-- statement:
--   For a finite ordered vertex type with at least three vertices, every graph with a crossing-free drawing has a drawable supergraph on the same vertices with exactly 3n − 6 edges. This isolates the embedding completion and Euler-count argument from the target’s maximality step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
