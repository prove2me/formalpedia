-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_has_triangulated_supergraph__p2m_9a9e5c69_ecec_470e_a422_cdf4baf4a7b3_a1
-- name    : WilliamsonShmoys.planarDrawing_has_triangulated_supergraph__p2m_9a9e5c69_ecec_470e_a422_cdf4baf4a7b3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:17:26.801431+00:00
-- url     : https://prove2.me/theorems/79d9077a-9097-422f-ae7f-37fe53526ec5
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every finite drawable simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_has_triangulated_supergraph__p2m_9a9e5c69_ecec_470e_a422_cdf4baf4a7b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (J : SimpleGraph V) (_ : DecidableRel J.Adj),
      H ≤ J ∧ HasPlanarDrawingOn J ∧
      3 * Fintype.card V - 6 = J.edgeFinset.card := by sorry
