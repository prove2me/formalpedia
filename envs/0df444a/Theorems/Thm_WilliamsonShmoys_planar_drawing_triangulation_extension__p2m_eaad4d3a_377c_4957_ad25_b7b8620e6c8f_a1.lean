-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:51.8617+00:00
-- url     : https://prove2.me/theorems/9715dea8-fcd2-44d6-b5ec-a796b1fa76e9
-- title:
--   Planar drawing extends to a maximal edge-count graph
-- statement:
--   Every finite drawable graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly 3n − 6. The proposed route extends the drawing to a triangulation and counts edges using Euler’s formula. This isolates the geometric extension and counting obligation needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
