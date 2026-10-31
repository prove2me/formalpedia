-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:35.379765+00:00
-- url     : https://prove2.me/theorems/a7de67a5-633c-46b0-b277-259b7a4818e8
-- title:
--   Triangulating extension of a planar drawing
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_2fdbe618_fdb5_40d5_afa9_43a53e53fa32_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
