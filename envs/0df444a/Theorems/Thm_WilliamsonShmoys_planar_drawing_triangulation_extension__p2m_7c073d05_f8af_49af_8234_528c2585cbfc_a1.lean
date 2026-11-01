-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:34.095719+00:00
-- url     : https://prove2.me/theorems/8a1d6513-cc2f-4bb4-9ed2-73bf53ea1ce0
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Every connected simply drawable graph with at least three vertices can be extended, using the same vertices, to a simply drawable graph whose edge count is exactly 3n−6. Edge inclusion lets the parent compare the original edge count with this triangulation count. A proof route adds edges inside faces until the drawing is maximal, then uses triangular faces and Euler's formula; the topological extension argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7c073d05_f8af_49af_8234_528c2585cbfc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
