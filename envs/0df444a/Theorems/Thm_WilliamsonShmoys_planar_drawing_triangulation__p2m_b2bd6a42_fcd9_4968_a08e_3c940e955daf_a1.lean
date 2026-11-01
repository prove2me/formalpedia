-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:56.262213+00:00
-- url     : https://prove2.me/theorems/aaf0613d-435c-4fad-8a76-ba323c101cda
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing can be extended, without adding vertices, to a planar triangulation whose edge count is exactly three times the number of vertices minus six. This is the main geometric obligation: extend the drawing by noncrossing edges until it is maximal planar, then apply the Euler face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
